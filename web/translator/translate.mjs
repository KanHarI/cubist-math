// Partial source translator. Unsupported syntax/foundations are explicit errors;
// no fallback axiom, old-kernel handle, or unchecked term enters this checker.
import {parse} from "../cubist/parser.mjs";
import {tacticSite,expressionSite} from "../cubist/link-sites.mjs";
import {sourceText} from "../cubical-source-text.mjs";
import {binaryLiteralSyntax} from "../cubist/binary-literals.mjs";
import {T,substituteTerm,substituteDimension} from "./core.mjs";
import {interval as I,face as F,latticeBudget} from "./lattice.mjs";
import {freeDimensions} from "./dimension-slots.mjs";
import {equalityRule,simplificationRule,findRewrite,SearchLimit} from "./proof-rewrite.mjs";
import {SearchFuel,SearchFuelExhausted,SEARCH_FUEL,recordSearch,emptySearchRecord} from "./fuel.mjs";
import {copySimpRegistry,orderedDefaultRules,resolveSimpSet,uniqueSimpRules} from "./simp-registry.mjs";
import {builtinTerm} from "./builtins.mjs";
import {tacticProof,PREMISE_ATTEMPT_LIMIT,dependentNote} from "./tactics.mjs";
import {Scope,SourceUnit,emptyRewriteWork} from "./elaboration.mjs";
import {Goal,Transition,steps,byConversion,composePaths} from "./proof-goals.mjs";
import {INDUCTIVE_TAGS,lowerInductive,resolveInductive} from "./inductive.mjs";
import {RECURSIVE,recursionSite,elaborateMatch,resolveRecursive,selfReference,matchedType} from "./match.mjs";
import {needsCompiling,compileMatch,continueMatch} from "./patterns.mjs";
import {HLevelSearch,HLevelUnproved,statement as hlevelStatement,levelName} from "./hlevel.mjs";
import {stem} from "./names.mjs";
import {determinesArguments,elaborateCall,isHole} from "./arguments.mjs";

// A tactic search (rw's for one rule, a simplification, simpa's two,
// hlevel's) spends counted fuel (fuel.mjs), never elapsed time. Its fuel
// starts when the search starts and covers matching candidates, trying rules
// and solving premises. It never covers elaborating user terms or later
// statements; rebuilding the proof, bounded by the number of rewrites, counts
// toward the declaration's fuel.

// JSON.stringify flattens shared core syntax before its result can be measured.
// Bound work during serialization so a compact DAG cannot exhaust the worker.
// Each node written spends one node of `fuel`, when a search asks.
const boundedStateKey = (term,fuel,kernel) => {
  let estimated=0,visits=0;
  const state=JSON.stringify(term,(key,value)=>{
    estimated+=key.length+4;
    if(typeof value==="string")estimated+=value.length+2;
    else if(typeof value==="number")estimated+=String(value).length;
    if(estimated>250000)throw new SearchLimit("Simplification term-size budget exceeded.");
    fuel?.spend("nodes");
    if((++visits&255)===0)kernel?.checkDeadline();
    return value;
  });
  if(state.length>250000)throw new SearchLimit("Simplification term-size budget exceeded.");
  return state;
};


// Universes (G0). U0, U3 are tier 0; UU0, UU3 tier 1 (ω + n); one more U per
// tier. A tier-0 level is a number; any other is a level object.
const universeConstant = name => {
  const match = /^(U+)([0-9]+)$/.exec(name);
  if (!match) return null;
  if (match[2].length > 1 && match[2][0] === "0") throw Error(`Malformed universe constant: ${name}.`);
  const tier = match[1].length - 1, value = Number(match[2]);
  return tier ? {tag:"LConst",tier,value} : value;
};
// A level below ω: every variable ranges over the natural numbers, and only a
// constant of tier 1 or above is not finite.

// The elaborator threads an explicit Scope (elaboration.mjs) through every
// term and proof statement. Its source unit carries the source text, module,
// simplification rules, inspector sink, freeze policy, work counters and name
// supply; nothing is swapped in translator fields for replays.
export class Translator {
  constructor({normalize=true,checker,onReference=null,onDeclaration=null,onDeclarationStart=null,
    onStep=null,simpRegistry,moduleName="source",freezeSuggestions=true,searchFuel=SEARCH_FUEL,declarationFuel,
    inspectSignature=null}={}) {
    // A declared type's signature as `print(inspect(T));` shows it, from the
    // program that admitted it (web/cubical-program.mjs).
    this.inspectSignature=inspectSignature;
    // The fuel limits of each tactic search and of each declaration (fuel.mjs).
    this.searchFuel=searchFuel;
    this.declarationFuel=declarationFuel;
    // Each proof statement that elaborates reports its goal and the proof of
    // that goal, for goal inspection and the elaboration view.
    this.onStep=onStep;
    // Offering "simp only" replacements reruns each simplification. Views that
    // cannot use the edit turn this off.
    this.freezeSuggestions=freezeSuggestions;
    // The checker is the elaborator (web/cubical-elaborator.mjs): every check
    // and query it answers is the instruction kernel's.
    if(!checker)throw Error("A translator needs a checker: the elaborator over a kernel.");
    this.checker=checker;
    this.normalize=normalize;
    this.localSources=new WeakMap();
    // An inspector record carries the context and dimensions of its scope and
    // the source aliases in `env`.
    this.references=onReference ? (node,term,scope,env)=>onReference(node,term,new Map(scope.context),
      new Map(scope.dimensions),[...(env??[])].flatMap(([name,value])=>{
        const source=this.localSources.get(value);
        return source?.name===name ? [{...source,term:value}] : [];
      })) : null;
    this.onDeclaration=onDeclaration;
    this.onDeclarationStart=onDeclarationStart;
    this.simpRegistry=copySimpRegistry(simpRegistry);
    this.moduleName=moduleName;
  }
  // A source unit of this translator. translate() makes one per module.
  unit(options={}) {
    return new SourceUnit({checker:this.checker,moduleName:this.moduleName,simpRegistry:this.simpRegistry,
      references:this.references,freezeSuggestions:this.freezeSuggestions,...options});
  }
  reference(scope,node,term,env=scope.env) {scope.unit.references?.(node,term,scope,env);}
  // Run a tactic search at a scope whose unit carries the search's own fuel,
  // shared by everything it does, premise searches included; `name` names it
  // in a message. A search already running at the scope is joined instead.
  // The fuel closes when the search ends, and the declaration records what
  // it spent.
  // `body(at, own)` learns whether it owns the search: an enclosing search's
  // diagnostic is the one to describe. With `shared`, fuel from searchFuelAt,
  // the body owns its search but spends that fuel, which its caller closes.
  search(scope,name,body,shared=null) {
    if(shared)return body(scope.withUnit(scope.unit.with({fuel:shared})),true);
    if(scope.unit.fuel?.open&&!scope.unit.fuel.declaration)return body(scope,false);
    const fuel=this.searchFuelAt(scope,name);
    try {return body(scope.withUnit(scope.unit.with({fuel})),true);}
    finally {fuel.close();}
  }
  // What a declaration-like unit spent: its kernel queries, and its searches'.
  fuelRecord(unit) {
    return {queries:unit.fuel.used.queries,searches:unit.searches.searches,most:{...unit.searches.most}};
  }
  searchFuelAt(scope,name) {
    return new SearchFuel(name,this.searchFuel,{parent:scope.unit.fuel,
      record:used=>recordSearch(scope.unit.searches,used)});
  }
  sourceBinding(node,term,scope) {
    const name=node.text??node.name;
    // A source alias gets its own syntax object, even for `let y = x`.
    // This keeps lexical labels from overwriting x or leaking into siblings.
    term={...term};scope=scope.alias(name,term);
    this.localSources.set(term,{name,start:node.start,end:node.end});
    this.reference(scope,{...node,name,isBinding:true},term);
    return scope;
  }
  // Interval names are cubical coordinates, never terms of a fabricated type.
  interval(n,env,budget=latticeBudget(()=>this.checker.kernel?.checkDeadline())) {
    budget.tick();
    if(n.kind==="number"&&(n.value===0||n.value===1))return n.value===0?I.zero:I.one;
    if(n.kind==="unary"&&n.operator==="-")return I.reverse(this.interval(n.operand,env,budget),budget);
    if(n.kind==="binary"&&["&","|"].includes(n.operator))
      return (n.operator==="&"?I.meet:I.join)(this.interval(n.left,env,budget),this.interval(n.right,env,budget),budget);
    // A coordinate on a face that fixes it is its endpoint there (Scope.onFace).
    if(n.kind==="name"&&env.get(n.name)?.tag==="Dimension") {
      const {name,endpoint}=env.get(n.name);
      return endpoint===undefined?I.variable(name,budget):endpoint?I.one:I.zero;
    }
    if(n.kind==="call"&&n.fn.kind==="name") {
      const args=n.args.map(a=>this.interval(a,env,budget));
      if(n.fn.name==="flip"&&args.length===1)return I.reverse(args[0],budget);
      if(n.fn.name==="meet"&&args.length===2)return I.meet(args[0],args[1],budget);
      if(n.fn.name==="join"&&args.length===2)return I.join(args[0],args[1],budget);
    }
    throw Error("Expected an interval coordinate: 0, 1, a coordinate name, -i, i & j or i | j (or flip, meet, join).");
  }
  cofibration(n,env,budget=latticeBudget(()=>this.checker.kernel?.checkDeadline())) {
    budget.tick();
    if(n.kind==="number"&&(n.value===0||n.value===1))return n.value===0?F.bottom:F.top;
    if(n.kind==="binary"&&["and","or"].includes(n.operator))return (n.operator==="and"?F.meet:F.join)(this.cofibration(n.left,env,budget),this.cofibration(n.right,env,budget),budget);
    if(n.kind==="call"&&n.fn.kind==="name"&&n.fn.name==="on"&&n.args.length===2) {
      const endpoint=n.args[1];
      if(endpoint.kind==="number"&&[0,1].includes(endpoint.value))return F.equalEndpoint(this.interval(n.args[0],env,budget),endpoint.value,budget);
    }
    throw Error("Expected a face formula: on(i, 0 or 1), and/or, 0 or 1.");
  }
  // A universe variable x < UU0 (G0): bound in the context at its bound, and
  // standing for the universe U(x) wherever the source names it. Only the
  // bound UU0 is admitted in this version.
  universeBinder(token,bound,scope) {
    if(bound?.kind!=="name"||bound.name!=="UU0")
      throw scope.unit.locate(Error("A universe variable's bound must be UU0, as in U < UU0."),bound);
    const name=scope.fresh(token.text);
    return {name,inner:this.sourceBinding(token,T.universe(T.variable(name)),scope.bind(name,T.bound))};
  }
  // The level of a universe expression: U3, UU0, a universe variable,
  // next(E) or max(E, F).
  levelOf(node,scope) {
    const universe=this.term(node,scope,null);
    if(universe.tag!=="U")
      throw scope.unit.locate(Error("Expected a universe: U0, UU0, a universe variable, next(E) or max(E, F)."),node);
    return universe.level;
  }
  dimensionBody(n,dim,scope,expected=null) {
    if(n.kind!=="lambda"||n.domain.kind!=="name"||n.domain.name!=="Interval")
      throw Error("Expected fun (i : Interval) => ... in a cubical binder.");
    return this.term(n.body,scope.bindDimension(dim).alias(n.name.text,{tag:"Dimension",name:dim}),expected);
  }
  // A result computes only if it uses no assumption: every assumption is a
  // postulate without computation rules. Name one path of definitions from
  // the result to an assumption, so the author can see where it enters.
  nonComputingMessage(subject,assumptions,term,type) {
    const label=name=>this.checker.assumptionLabels?.get(name)??name;
    const labels=[...new Set(assumptions.map(label))].sort();
    const target=[...assumptions].sort((a,b)=>label(a).localeCompare(label(b)))[0];
    const chain=this.assumptionChain(term,type,target).map(binding=>{
      const split=binding.indexOf("__"),module=split<0?null:binding.slice(0,split);
      const local=split<0?binding:binding.slice(split+2);
      return module&&module!==this.moduleName?`${local} (${module})`:local;
    });
    return `${subject} depends on non-computing assumptions: ${labels.join(", ")}. `+
      `Path to ${label(target)}: ${[...chain,label(target)].join(" → ")}.`;
  }
  assumptionChain(term,type,target,seen=new Set()) {
    const references=new Set(),visited=new WeakSet();
    const walk=node=>{
      if(!node||typeof node!=="object"||visited.has(node))return;
      visited.add(node);
      if(node.tag==="DefRef")references.add(node.name);
      for(const child of Array.isArray(node)?node:Object.values(node))walk(child);
    };
    walk(term);walk(type);
    for(const reference of references) {
      if(seen.has(reference)||seen.size>64)continue;
      seen.add(reference);
      const view=this.checker.definitionViews?.get(reference);
      if(view&&this.checker.requiredAssumptions?.(view.term,view.type).has(target))
        return [reference,...this.assumptionChain(view.term,view.type,target,seen)];
    }
    return [];
  }
  // `evaluate term expecting value;` normalizes a closed, assumption-free term
  // and requires its normal form to agree with the expected value's.
  evaluate(d,scope) {
    scope.spend("queries");
    const result=this.checker.verify(this.term(d.value,scope));
    const assumptions=result.native?.axioms??[...(this.checker.requiredAssumptions?.(result.term,result.type).keys()??[])];
    if(assumptions.length)throw Error(this.nonComputingMessage("The evaluated term",assumptions,result.term,result.type));
    scope.spend("queries");
    const expected=this.checker.verify(this.term(d.expected,scope));
    if(!scope.equal(result.type,expected.type))
      throw Error(`The evaluated term has type ${this.shown(result.type)}, but the expected value has type ${this.shown(expected.type)}.`);
    if(!scope.equal(result.normal,expected.normal))
      throw Error(`The term evaluates to ${this.shown(result.normal)}, not ${this.shown(expected.normal)}.`);
    return this.shown(result.normal);
  }
  // `print(evaluate(e));` shows the normal form of a closed, assumption-free
  // term, as `evaluate` computes one; `print(typeof(e));` its type; and
  // `print(inspect(e));` the term the kernel checked, in kernel notation. A
  // name shows what the CLI's inspect shows: a definition's checked body, or
  // a declared type's signature and its eliminator's clause types.
  printed(d,scope) {
    if(d.show==="evaluate") {
      scope.spend("queries");
      const result=this.checker.verify(this.term(d.value,scope));
      const assumptions=result.native.axioms;
      if(assumptions.length)throw Error(this.nonComputingMessage("The evaluated term",assumptions,result.term,result.type));
      return this.shown(result.normal);
    }
    const result=scope.infer(this.term(d.value,scope));
    if(d.show==="typeof")return this.shown(result.type);
    if(d.value.kind==="name") {
      let body=result.term;
      while(body.tag==="Lam"||body.tag==="LLam")body=body.body;
      if(body.tag==="Sort"&&this.inspectSignature)return this.inspectSignature(body.signature);
    }
    const definition=d.value.kind==="name"&&result.term.tag==="DefRef"?this.checker.definitionViews?.get(result.term.name):null;
    return this.checker.kernelText(definition?.term??result.term,1000);
  }
  // A term as messages show it: source names, generated suffixes removed.
  shown(term) {return this.checker.displayText?.(term,1000)??sourceText(term);}
  // Terms in one scope that a message shows, named together: a variable
  // reads alike in each, apart from every label any of them prints. Closed
  // terms share no variable, and are shown alone.
  shownTogether(terms) {return this.checker.displayTexts?.(terms,1000)??terms.map(term=>sourceText(term));}
  translate(source, imported=new Map()) {
    const module=this.unit({source});
    const ast=parse(source),env=new Map(imported),declarations=[],directives=[];
    for(const d of ast.items??ast.declarations) {
      if(d.kind==="evaluate") {
        const line=source.slice(0,d.start).split("\n").length;
        // An evaluation asks the kernel as a declaration does, with fuel of its own.
        const unit=module.declaration(this.declarationFuel);
        try {
          directives.push({kind:"evaluate",name:`at line ${line}`,status:"checked",start:d.start,
            normalText:this.evaluate(d,new Scope(unit,new Map(),env))});
        } catch(error) {
          directives.push({kind:"evaluate",name:`at line ${line}`,status:"not-translated",
            reason:error.message,start:d.start,failure:error.kind});
        }
        unit.fuel.close();
        directives.at(-1).searchFuel=this.fuelRecord(unit);
        continue;
      }
      if(d.kind==="print") {
        const line=source.slice(0,d.start).split("\n").length;
        const unit=module.declaration(this.declarationFuel);
        try {
          directives.push({kind:"print",name:`${d.show} at line ${line}`,status:"checked",start:d.start,
            text:this.printed(d,new Scope(unit,new Map(),env))});
        } catch(error) {
          directives.push({kind:"print",name:`${d.show} at line ${line}`,status:"not-translated",
            reason:error.message,start:d.start,failure:error.kind});
        }
        unit.fuel.close();
        directives.at(-1).searchFuel=this.fuelRecord(unit);
        continue;
      }
      if(d.kind==="simp_rule"||d.kind==="simp_set") {
        // Registering a rule searches its pattern, with search fuel; the
        // directive records what its searches spent.
        const unit=module.declaration(this.declarationFuel);
        try {
          if(d.kind==="simp_rule") {
            const rule=this.registeredSimpRule(d.rule,unit,env,d.priority);
            const existing=this.simpRegistry.defaults.get(rule.identity);
            if(existing&&existing.origin===rule.origin)
              throw Error(`Simplification rule ${d.rule.text} is already registered in this module.`);
            if(!existing||rule.priority>existing.priority)this.simpRegistry.defaults.set(rule.identity,rule);
          } else {
            if(this.simpRegistry.sets.get(d.name.text)?.origin===this.moduleName)
              throw Error(`Simplification set ${d.name.text} is already declared in this module.`);
            const rules=d.rules.map(token=>this.registeredSimpRule(token,unit,env,0));
            this.simpRegistry.sets.set(d.name.text,{origin:this.moduleName,
              rules:uniqueSimpRules(rules)});
          }
          directives.push({kind:d.kind,name:d.rule?.text??d.name.text,status:"checked",start:d.start});
        } catch(error) {
          directives.push({kind:d.kind,name:d.rule?.text??d.name.text,status:"not-translated",
            reason:error.message,start:d.start,failure:error.kind});
        }
        unit.fuel.close();
        directives.at(-1).searchFuel=this.fuelRecord(unit);
        continue;
      }
      if(d.kind==="inductive") { this.inductiveDeclaration(d,module,env,declarations);continue; }
      // Each declaration counts its own rewriting work and spends its own fuel.
      const unit=module.declaration(this.declarationFuel).with({declaring:d.name.text});
      this.onDeclarationStart?.(d);
      try {
        let expression=d.value;
        if(!expression) {
          expression={kind:"proof",type:d.type,statements:d.body};
          for(let j=d.params.length-1;j>=0;) {
            const group=d.params[j].group??j,members=[];
            while(j>=0&&(d.params[j].group??j)===group)members.unshift(d.params[j--]);
            const binder=members[0].bound?{bound:members[0].bound}:{domain:members[0].type};
            expression=members.length===1
              ? {kind:"lambda",name:members[0].name,...binder,body:expression}
              : {kind:"binderGroup",binderKind:"lambda",names:members.map(p=>p.name),
                ...binder,body:expression};
          }
        }
        // A body that is, as a whole, a match on a declared type may call the
        // declaration on a constructor's argument: its own name is a recursive
        // reference there. Only then is that argument's recursive result the
        // declaration's value on it.
        let bodyEnv=env;
        const own=d.params.length?d.params:d.valueParameters??[],site=recursionSite(d,own);
        if(site) {
          // Its parameters are known by their binders' tokens, and each is
          // recorded where it is bound (ownParameter), never looked up by name.
          const recursive={tag:"Recursive",source:d.name.text,params:own.map(p=>p.name.text),implicit:own.map(p=>!!p.implicit),
            tokens:own.map(p=>p.name),bindings:new Map(),site};
          bodyEnv=new Map(env).set(d.name.text,recursive).set(RECURSIVE,recursive);
        }
        const term=this.term(expression,new Scope(unit,new Map(),bodyEnv));
        // Normal forms are optional inspection output, not a prerequisite for
        // checking a declaration whose Nat value may have millions of successors.
        // The declaration's closing check, and its admission below, are
        // kernel questions like any other, on the declaration's fuel.
        unit.fuel.spend("queries");
        const checked=this.normalize?this.checker.verify(term):this.checker.infer(term);
        const native=checked.native;
        if(native&&!native.ok)throw Error(`Native cubical check rejected: ${native.error}`);
        if(d.computable) {
          const assumptions=native?.axioms??checked.native?.axioms??[];
          if(assumptions.length)throw Error(this.nonComputingMessage("This computable declaration",
            assumptions,checked.term,checked.type));
        }
        if(this.checker.define)unit.fuel.spend("queries");
        // Its parameters as the source declares them, for named arguments
        // and implicit parameters.
        const definition=this.checker.define?.(d.name.text,checked.term,checked.type,
          own.length?own.map(p=>({name:p.name.text,implicit:!!p.implicit})):null)??checked.term;
        this.checker.kernel?.checkDeadline();
        env.set(d.name.text,definition);
        declarations.push({name:d.name.text,status:native?"checked-native-cubical":"checked-cubical-fragment",term:checked.term,type:checked.type,normal:checked.normal,native});
      } catch(error) {
        // Remove a same-named imported symbol: a failed local declaration must
        // never silently refer to that other declaration in subsequent proofs.
        env.set(d.name.text,{tag:"Untranslated",name:d.name.text,binding:this.checker.bindingName?.(d.name.text)??d.name.text,reason:error.message});
        // `failure` classifies a checker rejection ("mismatch", "budget",
        // "deadline" or "other"), so callers need not read the reason.
        declarations.push({name:d.name.text,status:"not-translated",reason:error.message,
          errorStart:error.offset,errorEnd:error.sourceEnd,blockedBy:error.blockedBy,failure:error.kind});
      }
      declarations.at(-1).rewriteWork={...unit.work};
      // What the declaration asked of the kernel, and what its searches spent.
      unit.fuel.close();
      declarations.at(-1).searchFuel=this.fuelRecord(unit);
      this.onDeclaration?.(d,declarations.at(-1));
      // Diagnostic observers may reject a late result after cleanup. Such a
      // result must not remain available to subsequent declarations.
      if (declarations.at(-1).status === "not-translated")
        env.set(d.name.text,{tag:"Untranslated",name:d.name.text,binding:this.checker.bindingName?.(d.name.text)??d.name.text,reason:declarations.at(-1).reason});
    }
    return {declarations,env,directives,simpRegistry:this.simpRegistry,
      normalizationVisits:this.checker.steps};
  }
  // A binder of the declaration's own parameter, known by its token: the
  // binding it made, for recursion to recognize (match.mjs).
  ownParameter(token,scope) {
    const recursive=scope.env.get(RECURSIVE),index=recursive?.tokens.indexOf(token)??-1;
    if(index>=0)recursive.bindings.set(index,scope.env.get(token.text));
  }
  // An inductive declaration (L2.1): lowered to a signature and admitted in
  // its own transaction, as a definition is; it binds the type's name and
  // its constructors' names. A failed one binds each as untranslated.
  inductiveDeclaration(d,module,env,declarations) {
    const unit=module.declaration(this.declarationFuel);
    this.onDeclarationStart?.(d);
    const names=[d.name.text,...d.constructors.map(c=>c.name.text),...(d.result?.modifier&&d.result.modifier.kind!=="type"?[`${d.name.text}.squash`]:[])];
    const untranslated=reason=>{for(const name of names)env.set(name,{tag:"Untranslated",name,
      binding:this.checker.bindingName?.(d.name.text)??d.name.text,reason});};
    try {
      const lowered=lowerInductive(this,d,new Scope(unit,new Map(),env));
      for(const [name,value] of lowered.entries)env.set(name,value);
      declarations.push({name:d.name.text,status:"checked-native-cubical",inductive:lowered.record,
        term:lowered.former,type:lowered.former,native:{ok:true,axioms:[],extensions:lowered.extensions}});
    } catch(error) {
      untranslated(error.message);
      declarations.push({name:d.name.text,status:"not-translated",reason:error.message,
        errorStart:error.offset,errorEnd:error.sourceEnd,blockedBy:error.blockedBy,failure:error.kind});
    }
    declarations.at(-1).rewriteWork={...unit.work};
    unit.fuel.close();
    declarations.at(-1).searchFuel=this.fuelRecord(unit);
    this.onDeclaration?.(d,declarations.at(-1));
    if(declarations.at(-1).status==="not-translated")untranslated(declarations.at(-1).reason);
  }
  // A registration names an already checked rule; it records no reference.
  registeredSimpRule(token,module,env,priority=0) {
    const scope=new Scope(module.with({references:null}),new Map(),env);
    const term=this.term({kind:"name",name:token.text,start:token.start,end:token.end},scope,null);
    const identity=this.search(scope,"Registering a simplification rule",at=>{
      simplificationRule(at,term);
      return boundedStateKey(term,at.unit.fuel,this.checker.kernel);
    });
    return {term,identity,origin:module.moduleName,priority,sourceName:token.text};
  }
  selectedSimpRules(items,scope,only,without=[],witnessNames=[]) {
    const {unit,env}=scope;
    const witnesses=witnessNames.map(token=>{
      try {
        const proof=env.get(token.text);
        if(!proof||!this.localSources.has(proof))
          throw Error(`Simplification premise witness must be local: ${token.text}.`);
        scope.infer(proof);
        return proof;
      } catch(error) {throw unit.locate(error,token);}
    });
    const selected=only?[]:orderedDefaultRules(unit.simpRegistry);
    for(const item of items) {
      const set=item.value.kind==="name"&&!item.reverse
        ? resolveSimpSet(unit.simpRegistry,item.value.name):null;
      if(set)selected.push(...set.map(rule=>({...rule,
        sourceStart:item.start,sourceEnd:item.end})));
      else {
        let term;
        try {term=this.term(item.value,scope,null);}
        catch(error) {throw unit.locate(error,item);}
        selected.push({term,identity:boundedStateKey(term,null,this.checker.kernel),reverse:item.reverse,
          sourceText:unit.source.slice(item.value.start,item.value.end),
          sourceStart:item.start,sourceEnd:item.end});
      }
    }
    const excluded=new Set();
    for(const token of without) {
      const set=resolveSimpSet(unit.simpRegistry,token.text);
      if(set)for(const rule of set)excluded.add(rule.identity);
      else {
        try {
          const term=this.term({kind:"name",name:token.text,start:token.start,end:token.end},scope,null);
          excluded.add(this.search(scope,"Excluding a simplification rule",at=>{
            const identity=boundedStateKey(term,at.unit.fuel,this.checker.kernel);
            simplificationRule(at,term);
            return identity;
          }));
        } catch(error) {throw unit.locate(error,token);}
      }
    }
    let rules;
    const activePremises=[];
    // Premise search state for one simplification with one rule list. The
    // same instantiated premise recurs on every pass and on both endpoints,
    // so each outcome is remembered and a failed search is not repeated.
    const premiseState=()=>({attempts:0,exhausted:false,outcomes:new Map()});
    let premises=premiseState();
    const ruleNumbers=new Map();
    const ruleNumber=identity=>{
      if(!ruleNumbers.has(identity))ruleNumbers.set(identity,ruleNumbers.size);
      return ruleNumbers.get(identity);
    };
    // Premise search runs at the scope of the search that needs the premise,
    // and spends its fuel, so a freeze replay's premise work is the replay's.
    const solvePremise=(premise,owner,at)=>{
      if(activePremises.includes(owner)||activePremises.length>=2)return null;
      // The available rules depend on the rules already solving a premise.
      let key=null;
      try {
        key=`${[...activePremises,owner].map(ruleNumber).join(",")}:${
          boundedStateKey(premise,at.unit.fuel,this.checker.kernel)}`;
      } catch(error) {
        // A premise too large to remember is still searched, just not cached.
        if(!(error instanceof SearchLimit))throw error;
      }
      if(key!==null&&premises.outcomes.has(key))return premises.outcomes.get(key);
      // Premise search is speculative. Running out of attempts means this
      // conditional rule does not fire, like any other unproved premise.
      if(premises.attempts>=PREMISE_ATTEMPT_LIMIT) {premises.exhausted=true;return null;}
      premises.attempts++;
      at.spend("premises");
      at.unit.work.premiseAttempts++;
      activePremises.push(owner);
      let outcome=null;
      try {
        const available=rules.filter(rule=>!activePremises.includes(rule.identity));
        const {transition}=this.simplifyEqualityGoal(new Goal(premise,at),available);
        at.unit.work.premiseRewriteSteps+=transition.trace.length;
        const residual=at.nf(transition.next.target);
        if(residual.tag==="Path"&&!freeDimensions(residual.family).has(residual.dim)
          &&at.equal(residual.left,residual.right)) {
          const base=at.check(T.line(at.fresh("i"),residual.family,residual.left),
            transition.next.target);
          const witness=at.check(transition.rebuild(base),premise);
          at.unit.work.premiseProofs++;
          outcome={term:witness,rules:transition.trace.flatMap(step=>[step.rule,...step.premiseRules])};
        }
      } catch(error) {
        // A cycle or exhausted node, candidate or rewrite bound while proving
        // a premise leaves that premise unproved. Running out of the shared
        // search fuel, and kernel cancellation, still stop the whole
        // simplification.
        if(!(error instanceof SearchLimit))throw error;
      } finally {activePremises.pop();}
      if(key!==null)premises.outcomes.set(key,outcome);
      return outcome;
    };
    // Compile the rules after elaborating every user-written rule term, so
    // this phase's fuel covers it alone.
    rules=this.search(scope,"Preparing the simplification rules",at=>
      uniqueSimpRules(selected.filter(rule=>!excluded.has(rule.identity))).map(rule=>{
        let compiled;
        try {compiled=simplificationRule(at,rule.term,rule.reverse,witnesses,
          (premise,where)=>solvePremise(premise,rule.identity,where));}
        catch(error) {throw unit.locate(error,
          {start:rule.sourceStart,end:rule.sourceEnd});}
        const available=rule.sourceName&&env.get(rule.sourceName);
        let sourceText=rule.sourceText??null;
        if(!sourceText&&available) {
          try {
            if(boundedStateKey(available,null,this.checker.kernel)===rule.identity)
              sourceText=rule.sourceName;
          } catch(error) {
            // A large shadowing term only disables a source edit suggestion.
            if(!(error instanceof SearchLimit))throw error;
          }
        }
        return {...compiled,identity:rule.identity,reverse:!!rule.reverse,
          sourceStart:rule.sourceStart,sourceEnd:rule.sourceEnd,
          sourceText,displayName:sourceText??(rule.origin&&rule.sourceName
            ? `${rule.origin}.${rule.sourceName}`:"a checked rule")};
      }));
    // Premise search closes over this rule list. Freeze validation must replace
    // that list as well as the rules used by the outer simplifier traversal,
    // and must start from fresh premise outcomes and attempts.
    Object.defineProperty(rules,"withSubset",{value:(subset,run)=>{
      const previous=rules,previousPremises=premises;
      rules=subset;premises=premiseState();
      try {return run();}
      finally {rules=previous;premises=previousPremises;}
    }});
    Object.defineProperty(rules,"premiseSearchExhausted",{get:()=>premises.exhausted});
    return rules;
  }
  // `replay(subset, scope)` repeats a simplification with fewer rules. It runs
  // in a unit of its own, so its work is not counted as the declaration's.
  // Only a unit that records references asks for this: nothing else offers it.
  freezeSimplification(first,rules,trace,scope,replay) {
    const {unit}=scope;
    if(first.only||!unit.freezeSuggestions)return null;
    const used=new Set(trace.flatMap(step=>[step.rule,...step.premiseRules])
      .map(rule=>`${rule.identity}:${rule.reverse}`));
    const frozen=rules.filter(rule=>used.has(`${rule.identity}:${rule.reverse}`));
    if(frozen.some(rule=>!rule.sourceText))return null;
    // An unqualified name is parsed as a named set before a theorem term.
    // Suppress a suggestion whose spelling would select different rules.
    if(frozen.some(rule=>!rule.reverse&&unit.simpRegistry.sets.has(rule.sourceText)))return null;
    if(frozen.length<rules.length) {
      // Its fuel is its own too: only the inspector asks for a replay, and the
      // declaration must spend the same in every view.
      const replayScope=scope.withUnit(unit.with({work:emptyRewriteWork(),fuel:null,searches:emptySearchRecord()}));
      let valid=false;
      // An omitted rule can change a failed premise search and hence a later
      // rewrite. Replay must preserve the constructed proof as well as
      // its type: later statements may depend on that particular path.
      try {valid=rules.withSubset(frozen,()=>replay?.(frozen,replayScope)===true);}
      catch {valid=false;}
      if(!valid)return null;
    }
    const keyword=first.kind==="simpaOnly"?"simpa":"simp";
    let text=`${keyword} only [${frozen.map(rule=>`${rule.reverse?"<- ":""}${rule.sourceText}`).join(", ")}]`;
    if(first.witnesses?.length)text+=` with [${first.witnesses.map(token=>token.text).join(", ")}]`;
    if(first.at)text+=` at ${first.at.text} as ${first.as.text}`;
    if(first.using)text+=` using ${unit.source.slice(first.using.start,first.using.end)}`;
    text+=";";
    return {start:first.start,end:first.end,
      original:unit.source.slice(first.start,first.end),text};
  }
  // sym(p) and -p: the reversed path. A constant path is its own reversal.
  // Retain the ordinary path term so applying it to a large interval need not
  // distribute the reversal inside the native checker.
  reversePath(scope,p,spelling) {
    const type=scope.nf(scope.infer(p).type);
    if(type.tag!=="Path")throw Error(spelling==="-"?"-p reverses a path; found no path.":"sym requires a path.");
    if(p.tag==="PLam"&&!freeDimensions(p.body).has(p.dim)
      &&!freeDimensions(p.family).has(p.dim))return p;
    // Cubist equality has a constant carrier (dependent Path reversal
    // is checked by the core directly, rather than silently approximated).
    const i=scope.fresh("i"),result=T.line(i,type.family,T.at(p,I.reverse(I.variable(i))));
    return this.checker.ascribe && this.checker.kernel?.optimizations?.compactPaths !== false ? scope.ascribe(result,T.path(i,type.family,type.right,type.left)) : result;
  }
  // trans(p, q) and p ++ q: the composite path.
  concatenatePaths(scope,p,q,spelling) {
    const pt=scope.nf(scope.infer(p).type),qt=scope.nf(scope.infer(q).type);
    if(pt.tag!=="Path"||qt.tag!=="Path")throw Error(spelling==="++"?"p ++ q concatenates paths; found no path.":"trans requires paths.");
    scope.expect(pt.family,qt.family);
    if(!scope.equal(pt.right,qt.left))throw Error("Path endpoints do not match.");
    const i=scope.fresh("i"),j=scope.fresh("j");
    const result=T.line(j,pt.family,T.comp(i,pt.family,[
      {face:F.endpoint(j,0),term:pt.left},{face:F.endpoint(j,1),term:T.at(q,I.variable(i))},
    ],T.at(p,I.variable(j))));
    // Retain the mathematical endpoints in the inferred signature.
    // The native checker still verifies the composition and conversion.
    return this.checker.ascribe && this.checker.kernel?.optimizations?.compactPaths !== false ? scope.ascribe(result,T.path(j,pt.family,pt.left,qt.right)) : result;
  }
  term(n,scope,expected=null) {
    const result=this.termBody(n,scope,expected);
    if(scope.unit.references) {
      const {env,unit}=scope;
      let site;
      if(n.kind==="call" && n.fn.kind==="name" && !env.has(n.fn.name)) site=n.fn;
      else if(n.kind==="name" && !env.has(n.name)) site=n;
      else site=expressionSite(n);
      if(Number.isInteger(site?.start)) this.reference(scope,{...site,expressionSite:true,
        role:"language expression",description:`Checked expression: ${unit.source.slice(n.start,n.end).trim()}`},
        result);
    }
    return result;
  }
  // Numerals and the legacy induction syntax use the Nat in the source's
  // environment. Its declaration and admission belong to the imported module.
  naturalConstructors(scope) {
    const type=scope.nf(this.term({kind:"name",name:"Nat"},scope,null));
    const natural=type.tag==="Sort"&&this.checker.inductives?.get(type.signature);
    const zero=natural?.constructors.findIndex(c=>c.source==="zero"&&c.arity===0&&c.dims===0);
    const succ=natural?.constructors.findIndex(c=>c.source==="succ"&&c.arity===1&&c.dims===0);
    if(!natural||natural.slots.length||natural.constructors.length!==2||zero<0||succ<0)
      throw Error("Numerals and induction require an imported Nat with zero and succ constructors.");
    return {type,zero:T.constructor(zero,type,"zero"),succ:T.constructor(succ,type,"succ")};
  }
  termBody(n,scope,expected=null) {
    scope.checkDeadline();
    if(!n) throw Error("Missing source expression.");
    const {env}=scope;
    const tr=(x,e=expected)=>this.term(x,scope,e);
    const inferred=t=>scope.infer(t);
    switch(n.kind) {
      case "withUnfolding": {
        // The names must be checked definitions, and link as references; since
        // the conversion oracle's retirement they steer nothing, and the body
        // is checked as a definition of its own.
        scope.spend("queries");
        for(const hint of n.hints) {
          let value=env.get(hint.text);
          while(value?.tag==="App")value=value.fn;
          if(value?.tag!=="DefRef")throw Error(`No checked definition to unfold: ${hint.text}`);
          this.reference(scope,{...hint,name:hint.text},value,null);
        }
        return this.checker.scopedUnfolding(()=>tr(n.body),scope.context,expected,
          scope.dimensions,scope.unit.names);
      }
      case "pathApply": {
        // A path constructor at a point builds an element of its sort, so the
        // point's expected type names the constructor's instance: P(push(c) @ i).
        const head=n.left.kind==="call"&&n.left.fn.kind==="name"?n.left.fn:n.left;
        const constructor=expected&&head.kind==="name"&&env.get(head.name)?.tag==="InductiveConstructor"&&env.get(head.name).dims>0;
        const path=tr(n.left,constructor?expected:null);
        return T.at(path,this.interval(n.right,env));
      }
      case "pathLambda": {
        if(!expected)throw Error("path i => ... needs an expected Path or PathP type.");
        const goal=scope.nf(expected);
        if(goal.tag!=="Path")throw Error("path i => ... needs an expected Path or PathP type.");
        const dim=scope.fresh(n.dimension.text),inner=scope.bindDimension(dim);
        const family=substituteDimension(goal.family,goal.dim,I.variable(dim));
        const body=this.term(n.body,inner.alias(n.dimension.text,{tag:"Dimension",name:dim}),family);
        return T.line(dim,family,body);
      }
      case "along": {
        const family=tr(n.family,null),path=tr(n.path,null),value=tr(n.value,null);
        const type=scope.nf(inferred(path).type);
        if(type.tag!=="Path"||freeDimensions(type.family).has(type.dim))
          throw Error("along requires a homogeneous base path.");
        const dim=scope.fresh("i");
        return T.comp(dim,T.app(family,T.at(path,I.variable(dim))),[],value);
      }
      case "name": {
        // A binder _ binds nothing to refer to; a hole is a call's argument.
        if(isHole(n))throw Error("A hole _ stands for an argument of a call, which the call's other arguments or the type expected of it determine; anywhere else, write the term.");
        if(env.has(n.name)) {
          const value=env.get(n.name);
          if(value.tag==="Untranslated") {
            const error=Error(`Untranslated dependency: ${n.name}`);
            error.blockedBy=value.binding??value.name;
            throw error;
          }
          if(value.tag==="Dimension")throw Error("Interval coordinates can only be used in interval arguments.");
          // A declared type or constructor (L2.1), or the declaration's own name.
          if(INDUCTIVE_TAGS.has(value.tag))return resolveInductive(this,n,value,null,scope,expected);
          if(value.tag==="Recursive")return resolveRecursive(this,n,value,null,scope);
          this.reference(scope,n,value);
          return value;
        }
        const constant=universeConstant(n.name);
        if(constant!==null)return T.universe(constant);
        if(n.name==="Universe")throw Error("Universe was removed: bind a universe variable as U < UU0.");
        const builtin={Unit:T.unit,tt:T.point,Void:T.void};
        if(builtin[n.name])return builtin[n.name];
        // The declaration's own name, where it is not a recursive reference:
        // recursion exists only with declared types, under their option.
        if(scope.unit.declaring===n.name&&this.checker.kernel?.extensions?.h1)throw Error(selfReference(n.name));
        // The printer writes __U where an instance's universe is erased.
        if(/^__U[0-9]*$/.test(n.name))throw Error(`${n.name} stands for a universe that the printer could not show: write the universe in its place, such as U0 or a universe variable.`);
        throw Error(`Untranslated name: ${n.name}`);
      }
      case "number": {
        const natural=this.naturalConstructors(scope);
        let t=natural.zero;for(let i=0;i<n.value;i++)t=T.app(natural.succ,t);
        this.reference(scope,{...n,name:String(n.value)},t);return t;}
      case "binaryNumber": {
        const term=tr(binaryLiteralSyntax(n));
        this.reference(scope,{...n,name:`0b${n.digits}`},term);return term;
      }
      case "binderGroup": {
        if(n.bound)return tr(n.names.reduceRight((body,name)=>({kind:n.binderKind==="lambda"?"lambda":"forall",
          name,bound:n.bound,body,start:n.start,end:n.end}),n.body));
        const domain=tr(n.domain,null),kind=n.binderKind;
        let inner=scope,bodyExpected=expected;
        const names=[];
        for(const token of n.names) {
          const name=scope.fresh(token.text),variable=T.variable(name);
          if(kind==="lambda"&&bodyExpected) {
            const pi=inner.nf(bodyExpected);
            if(pi.tag!=="Pi")throw Error("Too many lambda binders for the expected type.");
            inner.expect(domain,pi.domain);
            bodyExpected=T.app(T.lam(pi.name,pi.domain,pi.body),variable);
          }
          inner=this.sourceBinding(token,variable,inner.bind(name,domain));
          this.ownParameter(token,inner);
          names.push(name);
        }
        let body=this.term(n.body,inner,kind==="lambda"?bodyExpected:null);
        const constructor=kind==="lambda"?T.lam:kind==="forall"?T.pi:T.sigma;
        for(const name of names.reverse())body=constructor(name,domain,body);
        return body;
      }
      case "lambda": case "forall": case "exists": {
        if(n.bound) {
          // Level quantification: λ (x < ω). t, or Π (x < ω). B.
          const {name,inner}=this.universeBinder(n.name,n.bound,scope);
          this.ownParameter(n.name,inner);
          let bodyExpected=null;
          if(n.kind==="lambda"&&expected) {
            const pi=scope.nf(expected);
            if(pi.tag!=="LPi")throw Error("A universe lambda needs a universe-generic type: forall U < UU0. …");
            bodyExpected=T.levelApply(T.levelLambda(pi.name,pi.body),T.variable(name));
          }
          const body=this.term(n.body,inner,bodyExpected);
          return (n.kind==="lambda"?T.levelLambda:T.levelPi)(name,body);
        }
        let domain=n.domain?tr(n.domain,null):null;
        if(n.kind==="lambda"&&!domain) {
          if(!expected)throw Error("Untyped lambda requires an expected function type.");
          const pi=scope.nf(expected);
          if(pi.tag!=="Pi")throw Error("Untyped lambda requires an expected function type.");
          domain=pi.domain;
        }
        const name=scope.fresh(n.name.text);
        const inner=this.sourceBinding(n.name,T.variable(name),scope.bind(name,domain));
        this.ownParameter(n.name,inner);
        let bodyExpected=null;
        if(n.kind==="lambda"&&expected) {
          const pi=scope.nf(expected);
          if(pi.tag==="Pi")bodyExpected=T.app(T.lam(pi.name,pi.domain,pi.body),T.variable(name));
        }
        const body=this.term(n.body,inner,bodyExpected);
        return (n.kind==="lambda"?T.lam:n.kind==="forall"?T.pi:T.sigma)(name,domain,body);
      }
      case "unary": {
        // -p is sym(p), whatever the name sym is bound to here.
        return this.reversePath(scope,tr(n.operand,null),"-");
      }
      case "binary": {
        if(["&","|"].includes(n.operator))
          throw Error(`${n.operator} combines interval coordinates, as in p @ i ${n.operator} j; it is not an operation on terms.`);
        const left=tr(n.left,null);
        // p ++ q is trans(p, q), whatever the name trans is bound to here.
        if(n.operator==="++")return this.concatenatePaths(scope,left,tr(n.right,null),"++");
        if(["->","and"].includes(n.operator)) return (n.operator==="->"?T.pi:T.sigma)(scope.fresh(),left,tr(n.right,null));
        if(n.operator==="or")return T.sum(left,tr(n.right,null));
        if(["+","*","<=","<"].includes(n.operator)) {
          const name=n.operator==="+"?"add":n.operator==="*"?"mul":n.operator==="<"&&env.has("isLt")?"isLt":"le";
          const first=n.operator==="<"&&name==="le"?{kind:"call",fn:{kind:"name",name:"succ"},args:[n.left]}:n.left;
          return tr({kind:"call",fn:{kind:"name",name},args:[first,n.right]},null);
        }
        if(n.operator==="=") {
          const type=n.carrier?tr(n.carrier,null):inferred(left).type;
          return T.path(scope.fresh("i"),type,left,tr(n.right,type));
        }
        throw Error(`Untranslated operator: ${n.operator}`);
      }
      case "projection": {
        // p.1 and p.2 are the kernel's projections; the family comes from the
        // checked type of p, so nothing is passed explicitly (HoTT A8).
        const pair=tr(n.value,null),type=inferred(pair).type;
        if(scope.nf(type).tag!=="Sigma")
          throw scope.unit.locate(Error(`Projection .${n.index} requires a dependent pair; found a value of type ${this.shown(type)}.`),
            {start:n.dot.start,end:n.digit.end});
        return n.index===1?T.first(pair):T.second(pair);
      }
      case "pair": {
        if(!expected)throw Error("Pair requires an expected type.");
        const sigma=scope.nf(expected);if(sigma.tag!=="Sigma")throw Error("Expected a Sigma type for pair.");
        const first=tr(n.left,sigma.domain), family=T.lam(sigma.name,sigma.domain,sigma.body);
        const result=T.pair(expected,first,tr(n.right,T.app(family,first)));
        if(scope.unit.references && Number.isInteger(n.tupleStart) && n.right.syntheticTuplePair) {
          const expand=node=>node.kind==="pair" ? `(${expand(node.left)}, ${expand(node.right)})`
            : scope.unit.source.slice(node.start,node.end).trim();
          const expansion=expand(n);
          for(const [name,start] of [["(",n.tupleStart],[")",n.tupleEnd]])
            this.reference(scope,{...n,name,start,end:start+1,role:"tuple macro",expansion,
              description:`Expands to ${expansion}.`},result);
        }
        return result;
      }
      case "call": {
        // Holes and named arguments: arguments the call determines (L4.1a).
        if(determinesArguments(n))return elaborateCall(this,n,scope,expected);
        if(n.fn.kind==="name"&&INDUCTIVE_TAGS.has(env.get(n.fn.name)?.tag))
          return resolveInductive(this,n.fn,env.get(n.fn.name),n.args,scope,expected);
        if(n.fn.kind==="name"&&env.get(n.fn.name)?.tag==="Recursive")
          return resolveRecursive(this,n.fn,env.get(n.fn.name),n.args,scope);
        const builtin=n.fn.kind==="name"&&!env.has(n.fn.name)?n.fn.name:null;
        if(builtin){const value=builtinTerm(this,builtin,n,scope,expected);if(value)return value;}
        // Each argument at its parameter's type, read from the function's
        // type once (arguments.mjs); a universe argument instantiates it.
        return elaborateCall(this,n,scope,expected);
      }
      case "induction": {
        // On any declared type: the clauses of a match, whose names may go on
        // to the induction hypotheses (match.mjs). Natural numbers' own form,
        // zero => …; succ h => …;, follows.
        if(!n.hypothesis){
          const value=tr(n.value,null),sort=scope.nf(inferred(value).type);
          if(sort.tag!=="Sort")throw scope.unit.locate(Error("induction requires a value of a declared type."),n.value);
          return elaborateMatch(this,n,value,sort,scope,expected);
        }
        // Binders keep their source names, so the checked term reads as written.
        const natural=this.naturalConstructors(scope),type=natural.type;
        const value=tr(n.value,type),k=scope.fresh(n.index?.text),ih=scope.fresh(n.hypothesis?.text);
        // Without `as`, the motive is constant and the predecessor unnamed.
        const stepScope=n.index?this.sourceBinding(n.index,T.variable(k),scope.bind(k,type)):scope.bind(k,type);
        const motiveBody=this.term(n.type,stepScope,null),motive=T.lam(k,type,motiveBody);
        const zero=tr(n.base,T.app(motive,natural.zero));
        const hypothesisScope=this.sourceBinding(n.hypothesis,T.variable(ih),stepScope.bind(ih,motiveBody));
        const step=T.lam(k,type,T.lam(ih,motiveBody,this.term(n.step,hypothesisScope,T.app(motive,T.app(natural.succ,T.variable(k))))));
        return T.app(T.eliminator(type.signature,motive,[zero,step]),value);
      }
      case "patternMatch": return continueMatch(this,n,scope,{expected});
      case "match": {
        // Several values, nested patterns, variables and _ compile to
        // matches on one value each (patterns.mjs).
        if(n.values)return compileMatch(this,n,scope,{expected,typeOf:(value,at)=>matchedType(this,at,value)});
        const value=tr(n.value,null),type=inferred(value).type,sum=scope.nf(type);
        const declared=sum.tag==="Sort"&&n.clauses?matchedType(this,scope,value):null;
        if(declared&&needsCompiling(this,n,new Set(declared.constructors.map(constructor=>constructor.name)),scope))
          return compileMatch(this,n,scope,{expected,typeOf:(value,at)=>matchedType(this,at,value)});
        // A declared type's value (L2.2a); otherwise the legacy match on a sum.
        if(sum.tag==="Sort")return elaborateMatch(this,n,value,sum,scope,expected);
        // Declared types are mentioned only where the kernel admits them (H1).
        if(sum.tag!=="Sum")throw Error(this.checker.kernel?.extensions?.h1
          ?"match requires a value of a declared type, or of a sum.":"match requires a sum type.");
        if(!n.leftBody||!n.type)throw Error("A match on a sum has a return type and the clauses left x => …; right y => ….");
        // Binders keep their source names, as induction's do.
        const name=scope.fresh(n.motiveName?.text),inner=scope.bind(name,type);
        const motive=T.lam(name,type,this.term(n.type,
          n.motiveName?inner.alias(n.motiveName.text,T.variable(name)):inner,null));
        const branch=side=>{
          const local=scope.fresh(n[side].text),domain=sum[side],variable=T.variable(local);
          const injection=(side==="left"?T.inl:T.inr)(type,variable);
          return T.lam(local,domain,this.term(n[side+"Body"],
            scope.bind(local,domain).alias(n[side].text,variable),T.app(motive,injection)));
        };
        return T.sumrec(motive,branch("left"),branch("right"),value);
      }
      case "unpack": {
        const value=tr(n.value,null),sigma=scope.nf(inferred(value).type);
        if(sigma.tag!=="Sigma")throw Error("unpack requires a dependent pair.");
        const goal=tr(n.type,null);
        const body=this.term(n.body,
          scope.alias(n.left.text,T.first(value)).alias(n.right.text,T.second(value)),goal);
        scope.check(body,goal);
        return body;
      }
      case "proof": {
        const type=tr(n.type,null);
        const term=this.block(n.statements,new Goal(type,scope));
        const checked=scope.check(term,type);
        return scope.ascribe(checked,type);
      }
      default:throw Error(`Untranslated syntax: ${n.kind}`);
    }
  }
  block(statements,goal) {
    try {
      const proof=this.blockBody(statements,goal);
      // The proof of the following statements is part of this one's proof.
      this.onStep?.({statement:statements[0],next:statements[1]??null,goal,proof});
      return proof;
    }
    catch(error) {
      throw goal.scope.unit.locate(error,statements[0]);
    }
  }
  // A statement makes a transition from the goal (proof-goals.mjs), and the
  // statements after it prove the goal that remains.
  blockBody(statements,goal) {
    if(!statements.length)throw Error("Proof block has no conclusion.");
    const [first,...rest]=statements;
    const proof=tacticProof(this,first,rest,goal);
    if(proof!==undefined)return proof;
    throw Error(`Proof tactic not yet translated: ${first.kind}`);
  }
  // One rw rule: rewrite its selected occurrence in the remaining goal.
  // `rewrites` collects {side, rule} for each rule's rewrite, for diagnostics.
  rewriteGoal(transition,first,item,rewrites=[]) {
    const {scope}=transition.goal,path=transition.next.equality();
    if(!path)throw Error("rw requires a homogeneous equality goal.");
    const rule=equalityRule(scope,this.term(item.value,scope,null),item.reverse);
    // The search's fuel covers this rule's search only: not elaborating the
    // rule, the statements after rw, or rebuilding the proof afterwards.
    let target=first.target;
    // No such occurrence: the user's error, with the goal it was sought in.
    const missing=(eligible,unsupported)=>Error(`${unsupported
      ? "Rewrite match occurs in an unsupported dependent position."
      : `Rewrite occurrence ${first.occurrence} was not found (${eligible} eligible matches).`}${
      this.residual(transition.next,rewrites)}`);
    const changed=this.search(scope,"rw",at=>{
      const find=(side,occurrence)=>findRewrite(at,path[side==="lhs"?"left":"right"],path.family,rule,occurrence,"preorder");
      // The rewrite made, while the search's fuel is open.
      const made=found=>{at.spend("rewrites");return found;};
      if(target) {
        const only=find(target,first.occurrence);
        if(!only.found)throw missing(only.eligible,only.unsupported);
        return made(only.found);
      }
      // Count eligible occurrences through the left endpoint, then the right.
      const left=find("lhs",first.occurrence);
      if(left.found) {target="lhs";return made(left.found);}
      const right=find("rhs",first.occurrence-left.eligible);
      if(!right.found)throw missing(left.eligible+right.eligible,left.unsupported||right.unsupported);
      target="rhs";
      return made(right.found);
    });
    rewrites.push({side:target,rule:{displayName:`${item.reverse?"<- ":""}${
      scope.unit.source.slice(item.value.start,item.value.end)||"a rule"}`}});
    const next=T.path(scope.fresh("i"),path.family,
      target==="lhs"?changed.after:path.left,
      target==="rhs"?changed.after:path.right);
    return transition.extend(steps.composition(scope,target,changed.witness),transition.next.with(next));
  }
  // The statements after a tactic prove the goal it leaves. At the end of a
  // block that goal must hold by conversion; `unresolved` makes the error.
  remaining(rest,next,unresolved) {
    if(rest.length)return this.block(rest,next);
    const proof=byConversion(next);
    if(!proof)throw unresolved();
    return proof;
  }
  // hlevel; closes a goal that states an h-level, IsContr, IsProp, IsSet or
  // HasLevel, or an equality in a proposition, from the lemmas
  // of library/hlevels.cubist, evidence in scope and the hints after `with`
  // (web/translator/hlevel.mjs). The search is untrusted; the kernel checks the
  // proof it builds. As with simpa, the hints are elaborated before the
  // search's fuel starts, and the proof is checked after it ends.
  hlevel(first,goal,scope) {
    try {scope.infer(T.levelApply({tag:"DefRef",name:"hlevels__HasLevel"},0));}
    catch(error) {
      if(!/^Unknown checked cubical definition/.test(error.message))throw error;
      throw Error("hlevel uses the library module hlevels: add import hlevels;");
    }
    const hints=first.hints.map(node=>{
      const term=this.term(node,scope,null),type=scope.infer(term).type;
      if(hlevelStatement(type))return {term,type};
      if(scope.nf(type).tag==="Pi")
        throw Error(`hlevel does not use quantified hints yet: apply ${this.shown(term)} to its arguments.`);
      throw Error(`The hint ${this.shown(term)} has type ${this.shown(type)}, which states no h-level.`);
    });
    // Evidence that local definitions name (let, obtain): source names
    // bound to terms that are not variables of the context, which the search
    // enumerates itself.
    const locals=[];
    for(const bound of scope.env.values()) {
      if(!this.localSources.has(bound)||bound.tag==="Var"&&scope.context.has(bound.name))continue;
      const type=scope.infer(bound).type;
      if(hlevelStatement(type))locals.push({term:bound,type});
    }
    const proof=this.search(scope,"hlevel",at=>{
      const search=new HLevelSearch(at,hints,term=>this.shown(term),locals);
      const stated=hlevelStatement(goal.target);
      try {
        if(stated)return search.prove(stated.level,stated.universe,stated.type);
        const path=goal.equality();
        if(!path)throw Error(`hlevel proves IsContr, IsProp, IsSet or HasLevel, or an equality in a proposition; the goal is ${this.shown(goal.target)}.`);
        const sort=at.nf(at.infer(path.family).type);
        if(sort.tag!=="U")throw Error("hlevel needs the type of the equality's sides to be in a universe.");
        return T.app(T.app(search.prove(0,sort.level,path.family),path.left),path.right);
      } catch(error) {
        if(!(error instanceof HLevelUnproved))throw error;
        // Each variable the search introduced for a binder is shown by that
        // binder's name.
        const shown=(term,names)=>this.shown([...names].reduce((renamed,[name,binder])=>
          substituteTerm(renamed,name,T.variable(stem(binder))),term));
        const needs=error.chain.slice(1).map(step=>`${shown(step.type,step.names)} to be ${levelName(step.level)}`
          +(step.binder?` for every ${stem(step.binder.name)} : ${shown(step.binder.domain,step.names)}`:""));
        throw Error(`hlevel could not prove ${this.shown(goal.target)}${needs.length?`: it needs ${needs.join(", which needs ")}`:""}; ${error.reason}.`);
      }
    });
    return this.conclude(first,new Transition(goal),proof,()=>({
      description:`Checked h-level evidence${hints.length?` with ${hints.length} hint${hints.length===1?"":"s"}`:""}.`}));
  }
  // Rebuild a proof of a transition's remaining goal into a checked proof of
  // its goal, which the tactic's keyword links to.
  conclude(first,transition,proof,details,trace=[]) {
    const {scope,target}=transition.goal,result=transition.rebuild(proof);
    scope.check(result,target);
    if(scope.unit.references)this.recordTactic(first,scope,result,details(result),trace);
    return result;
  }
  // Link a tactic's keyword to the checked proof it built, and each traced
  // rewrite to its witness.
  recordTactic(first,scope,proof,details,trace=[]) {
    const site=tacticSite(first);
    this.reference(scope,{...site,...details},proof);
    for(const [index,step] of trace.entries()) {
      const rule=step.rule.displayName;
      this.reference(scope,{name:`simp step ${index+1}`,start:site.start,end:site.end,
        role:"simplification step",expansionIndex:index+1,
        traceParent:site.start,
        description:`${step.phase??"goal"} ${step.side}: checked rewrite ${index+1} using ${step.rule.reverse?"<- ":""}${rule}; ${step.visits} nodes visited.${step.premiseRules.length
          ? ` Premise simplified using ${[...new Set(step.premiseRules.map(item=>item.displayName))].join(", ")}.`:""}`},
        step.witness);
    }
  }
  // simpa compares two simplified types. When matches were skipped in a
  // dependent position, that is the likeliest reason they still differ.
  checkSimplified(term,type,scope,dependent) {
    try {return scope.check(term,type);}
    catch(error) {
      if(dependent&&typeof error?.message==="string")error.message+=dependentNote;
      throw error;
    }
  }
  // Search one term for the first rule application, children before parents.
  // Rule errors point to the selected rule's source when it has one.
  findSimplification(root,carrier,rules,scope) {
    try {return findRewrite(scope,root,carrier,rules,1,"postorder");}
    catch(error) {
      const rule=error.rewriteRule;
      throw scope.unit.locate(error,rule?.sourceStart===undefined?null:
        {start:rule.sourceStart,end:rule.sourceEnd});
    }
  }
  // A goal for a diagnostic (HoTT A6): its target in source syntax, bounded
  // in length.
  goalText(goal,width=160) {
    try {return this.checker.displayGoal?.(goal.scope.shownContext([goal.target]),goal.target,null,width).goal??sourceText(goal.target);}
    catch {return "(too large to show)";}
  }
  // Two goals one diagnostic shows, named together when they share a scope,
  // as displayGoal names a goal and the term built for it.
  goalTexts(goal,other,width=160) {
    if(goal.scope!==other.scope||!this.checker.displayGoal)return [this.goalText(goal,width),this.goalText(other,width)];
    try {
      const shown=this.checker.displayGoal(goal.scope.shownContext([goal.target,other.target]),goal.target,other.target,width);
      return [shown.goal,shown.built];
    } catch {return ["(too large to show)","(too large to show)"];}
  }
  // What a search's rewrites did: the sides they changed and the rules that
  // fired, in order. A step is {side, rule}, as in a simplification's trace.
  rewriteSummary(trace) {
    if(!trace.length)return "No rule fired.";
    const sides=new Set(trace.map(step=>step.side));
    const where=sides.has("type")?"the type":sides.size>1?"both sides":sides.has("lhs")?"the left side":"the right side";
    const rules=[...new Set(trace.map(step=>step.rule.displayName))];
    return `${trace.length} rewrite${trace.length===1?"":"s"} changed ${where}, using ${rules.join(", ")}.`;
  }
  residual(goal,trace) {
    const shown=this.goalText(goal);
    return ` Remaining goal: ${shown}${shown.endsWith("…")?"":"."} ${this.rewriteSummary(trace)}`;
  }
  // A term for a diagnostic, in source syntax, bounded in length.
  termText(term,width=160) {
    try {return this.checker.displayText?.(term,width)??sourceText(term);}
    catch {return "(too large to show)";}
  }
  // Terms one diagnostic shows, named together, each bounded in length.
  termTexts(terms,width=160) {
    try {return this.checker.displayTexts?.(terms,width)??terms.map(term=>sourceText(term));}
    catch {return terms.map(()=>"(too large to show)");}
  }
  // A search stopped by a limit or by its fuel says where it stopped, once:
  // an enclosing search does not add its own goal.
  stopped(error,goal,trace,describe=true) {
    if((error instanceof SearchLimit||error instanceof SearchFuelExhausted)&&!error.residual) {
      error.stoppedAt??={goal,trace};
      if(describe) {
        this.describe(error,this.residual(goal,trace));
        error.residual=true;
      }
    }
    return error;
  }
  // Add to a message, before the source position locate() put at its end.
  describe(error,text) {
    const at=Number.isInteger(error.offset)?/ at \d+:\d+$/.exec(error.message):null;
    error.message=at?`${error.message.slice(0,at.index)}${text}${at[0]}`:error.message+text;
  }
  // A simplification's rules, selected and prepared: a search of their own,
  // which, stopped, stops the tactic with its goal unchanged.
  preparedRules(first,scope,goal) {
    try {return this.selectedSimpRules(first.rules,scope,first.only,first.without,first.witnesses);}
    catch(error) {throw this.stopped(error,goal,[]);}
  }
  // simpa's search stopped in one of its two simplifications: say which, where
  // it stopped, and how far the supplied type got when the goal's stopped.
  simpaStopped(error,phase,supplied) {
    if(!error.stoppedAt||error.residual)return error;
    const {goal,trace}=error.stoppedAt;
    const [shown,done]=supplied?this.goalTexts(goal,supplied.transition.next):[this.goalText(goal),null];
    let text=` ${phase} stopped at ${shown}${shown.endsWith("…")?"":"."} ${this.rewriteSummary(trace)}`;
    if(supplied) {
      text+=` The supplied type had simplified to ${done}${done.endsWith("…")?"":"."} ${
        this.rewriteSummary(supplied.transition.trace)}`;
    }
    this.describe(error,text);
    error.residual=true;
    return error;
  }
  // The goal came back to a state it was in `since` rewrites into the trace:
  // the rules that fired from there on make the cycle.
  cycle(since,trace) {
    const rules=[...new Set(trace.slice(since).map(step=>step.rule.displayName))];
    const count=trace.length-since;
    const names=rules.length>1?`${rules.slice(0,-1).join(", ")} and ${rules.at(-1)}`:rules[0];
    return new SearchLimit(`Simplification cycle detected in the selected rules. ${names} returned the goal to `
      +`where it was ${count} rewrite${count===1?"":"s"} earlier.`);
  }
  // Simplify a type goal as a whole. Its plan transports along the composite
  // of the rewrites' paths of types.
  // `fuel`, when given, is a search's the caller shares between several; with
  // `describe` false, a search that stops only records where
  // (error.stoppedAt), for the caller to describe.
  simplifyTypeTerm(goal,rules,fuel=null,describe=true) {
    const {scope}=goal,trace=[];
    let current=goal.target,dependent=false;
    this.search(scope,"simp",(at,own)=>{
      try {
        const carrier=at.nf(at.infer(goal.target).type);
        if(carrier.tag!=="U")throw Error("General simplification requires a type-valued goal.");
        const states=new Map();
        while(true) {
          at.checkDeadline();
          const state=boundedStateKey(current,at.unit.fuel,this.checker.kernel);
          if(states.has(state))throw this.cycle(states.get(state),trace);
          states.set(state,trace.length);
          // A match in a dependent position is skipped, not an error.
          const {found,unsupported}=this.findSimplification(current,carrier,rules,at);
          dependent=unsupported;
          if(!found)break;
          if(trace.length>=64)throw new SearchLimit("Simplification rewrite budget exceeded.");
          at.spend("rewrites");
          current=found.after;
          trace.push({side:"type",rule:found.rule,witness:found.witness,visits:found.visits,
            premiseRules:found.premiseRules});
        }
      } catch(error) {throw own?this.stopped(error,goal.with(current),trace,describe):error;}
    },fuel);
    // Compose after the search, outside its fuel.
    let witness=null;
    for(const step of trace)witness=witness?composePaths(scope,witness,step.witness):step.witness;
    return {transition:new Transition(goal,goal.with(current),witness?[steps.transport(witness)]:[],trace),
      dependent};
  }
  // Simplify an equality goal at its endpoints. Each rewrite is one
  // composition step of the plan.
  simplifyEqualityGoal(goal,rules,fuel=null,describe=true) {
    const {scope}=goal;
    let transition=new Transition(goal),dependent=false,failures=[];
    this.search(scope,"simp",(at,own)=>{
      const states=new Map();
      try {
        while(true) {
          at.checkDeadline();
          const path=transition.next.at(at).equality();
          if(!path)throw Error("simp only requires a homogeneous equality goal.");
          const state=boundedStateKey([path.left,path.right],at.unit.fuel,this.checker.kernel);
          if(states.has(state))throw this.cycle(states.get(state),transition.trace);
          states.set(state,transition.trace.length);
          for(const rule of rules)rule.clearDiagnostic?.();
          let selected=null;
          dependent=false;
          for(const side of ["lhs","rhs"]) {
            // A match in a dependent position is skipped: the other endpoint, and
            // a goal that already holds by conversion, remain available.
            const {found,unsupported}=this.findSimplification(side==="lhs"?path.left:path.right,
              path.family,rules,at);
            dependent||=unsupported;
            if(found) {selected={side,result:found};break;}
          }
          if(!selected) {
            failures=rules.flatMap(rule=>{
              const diagnostic=rule.diagnostic?.();
              return diagnostic?[{rule,...diagnostic}]:[];
            });
            break;
          }
          if(transition.trace.length>=64)throw new SearchLimit("Simplification rewrite budget exceeded.");
          at.spend("rewrites");
          const {side,result}=selected;
          const next=T.path(scope.fresh("i"),path.family,
            side==="lhs"?result.after:path.left,
            side==="rhs"?result.after:path.right);
          // Rebuilding composes checked paths after the search, possibly after
          // later statements, and spends the declaration's fuel, not the search's.
          transition=transition.extend(steps.composition(at,side,result.witness),goal.with(next),
            {side,rule:result.rule,witness:result.witness,visits:result.visits,premiseRules:result.premiseRules});
        }
      } catch(error) {throw own?this.stopped(error,transition.next,transition.trace,describe):error;}
    },fuel);
    // `dependent` describes the final pass: a remaining match was skipped.
    return {transition,failures,dependent};
  }
}
