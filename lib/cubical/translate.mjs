import {withNativeReferences} from "./equivalence.mjs";
import {halfAdjointEquiv,publicUnivalencePath,publicUnivalenceBeta} from "./public-equivalence.mjs";
import {libraryAssumption} from "../../web/cubical-assumptions.mjs";
// Partial source translator. Unsupported syntax/foundations are explicit errors;
// no fallback axiom, old-kernel handle, or unchecked term enters this checker.
import {parse} from "../../web/mathscript/parser.mjs";
import {cubicalText} from "../../web/cubical-notation.mjs";
import {binaryLiteralSyntax} from "../../web/mathscript/binary-literals.mjs";
import {Checker,T,fill,substituteDimension} from "./core.mjs";
import {interval as I,face as F,latticeBudget} from "./lattice.mjs";
import {freeDimensions} from "./dimension-slots.mjs";
import {equalityRule,simplificationRule,findRewrite,rewriteFirst,SearchLimit,SearchTimeout} from "./proof-rewrite.mjs";
import {copySimpRegistry,orderedDefaultRules,resolveSimpSet,uniqueSimpRules} from "./simp-registry.mjs";
import {dependentPathToTransport,transportToDependentPath} from "./path-over.mjs";
import {pushout} from "./pushouts.mjs";
import {Scope,SourceUnit,emptyRewriteWork} from "./elaboration.mjs";
import {Goal,Transition,steps,reflexivity,byConversion,composePaths} from "./proof-goals.mjs";

// The elapsed-time limit of one tactic search: matching candidates, trying
// rules and solving premises. It starts when that search starts. It never
// covers elaborating user terms, later statements, or rebuilding the proof,
// which is bounded by the number of rewrites or calc steps.
const SEARCH_TIME_LIMIT_MS = 1000;
const searchDeadline = () => performance.now() + SEARCH_TIME_LIMIT_MS;
// A conditional rule whose premises cannot be proved stops firing after this
// many distinct premise searches in one simplification; it does not fail it.
const PREMISE_ATTEMPT_LIMIT = 64;

// JSON.stringify flattens shared core syntax before its result can be measured.
// Bound work during serialization so a compact DAG cannot exhaust the worker.
const boundedStateKey = (term,deadline,kernel) => {
  let estimated=0,visits=0;
  const state=JSON.stringify(term,(key,value)=>{
    estimated+=key.length+4;
    if(typeof value==="string")estimated+=value.length+2;
    else if(typeof value==="number")estimated+=String(value).length;
    if(estimated>250000)throw new SearchLimit("Simplification term-size budget exceeded.");
    if((++visits&255)===0) {
      if(performance.now()>deadline)throw new SearchTimeout("Simplification elapsed-work budget exceeded.");
      kernel?.checkDeadline();
    }
    return value;
  });
  if(state.length>250000)throw new SearchLimit("Simplification term-size budget exceeded.");
  return state;
};

const dependentNote = " Some rule matches were skipped because they occur in a dependent "+
  "position; rewrite there with an explicit cong context.";
// The keyword of each tactic whose checked proof the inspector links to.
const tacticKeywords = {calc:"calc",rw:"rw",simpOnly:"simp",simpaOnly:"simpa"};

// Templates store a sequence of ordinary universe lambdas. Expand every
// leading group so specialization and inspection see the same parameters.
const expandUniverseBinders = expression => {
  if(!expression?.domain || expression.domain.kind!=="name" || expression.domain.name!=="Universe")
    return expression;
  if(expression.kind==="lambda")
    return {...expression,body:expandUniverseBinders(expression.body)};
  if(expression.kind==="binderGroup"&&expression.binderKind==="lambda") {
    let body=expandUniverseBinders(expression.body);
    for(const name of [...expression.names].reverse())
      body={kind:"lambda",name,domain:expression.domain,body};
    return body;
  }
  return expression;
};

// The elaborator threads an explicit Scope (elaboration.mjs) through every
// term and proof statement. Its source unit carries the source text, module,
// simplification rules, inspector sink, freeze policy, work counters and name
// supply; nothing is swapped in translator fields for templates or replays.
export class Translator {
  constructor({normalize=true,nativeCheck=null,checker=new Checker(),onReference=null,onDeclaration=null,onDeclarationStart=null,
    simpRegistry,moduleName="source",freezeSuggestions=true}={}) {
    // Offering "simp only" replacements reruns each simplification. Views that
    // cannot use the edit, such as template inspection, turn this off.
    this.freezeSuggestions=freezeSuggestions;
    this.checker=checker;
    this.normalize=normalize;this.nativeCheck=nativeCheck;
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
  // A source unit of this translator. translate() makes one per module;
  // callers inspecting a template make their own.
  unit(options={}) {
    return new SourceUnit({checker:this.checker,moduleName:this.moduleName,simpRegistry:this.simpRegistry,
      references:this.references,freezeSuggestions:this.freezeSuggestions,...options});
  }
  reference(scope,node,term,env=scope.env) {scope.unit.references?.(node,term,scope,env);}
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
    if(n.kind==="name"&&env.get(n.name)?.tag==="Dimension")return I.variable(env.get(n.name).name,budget);
    if(n.kind==="call"&&n.fn.kind==="name") {
      const args=n.args.map(a=>this.interval(a,env,budget));
      if(n.fn.name==="flip"&&args.length===1)return I.reverse(args[0],budget);
      if(n.fn.name==="meet"&&args.length===2)return I.meet(args[0],args[1],budget);
      if(n.fn.name==="join"&&args.length===2)return I.join(args[0],args[1],budget);
    }
    throw Error("Expected an interval coordinate, 0, 1, flip, meet or join.");
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
  dimensionBody(n,dim,scope,expected=null) {
    if(n.kind!=="lambda"||n.domain.kind!=="name"||n.domain.name!=="Interval")
      throw Error("Expected fun (i : Interval) => ... in a cubical binder.");
    return this.term(n.body,scope.bindDimension(dim).alias(n.name.text,{tag:"Dimension",name:dim}),expected);
  }
  // A template keeps the source unit it was defined in: its text, module and
  // simplification rules apply wherever it is specialized.
  schema(expression,env,unit) {
    expression=expandUniverseBinders(expression);
    return expression.kind==="lambda"&&expression.domain?.kind==="name"&&expression.domain.name==="Universe"
      ? {tag:"UniverseSchema",parameter:expression.name.text,body:expression.body,
        env:new Map(env),simpRegistry:copySimpRegistry(unit.simpRegistry),moduleName:unit.moduleName,
        source:unit.source} : null;
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
    const result=this.checker.verify(this.term(d.value,scope));
    const assumptions=result.native?.axioms??[...(this.checker.requiredAssumptions?.(result.term,result.type).keys()??[])];
    if(assumptions.length)throw Error(this.nonComputingMessage("The evaluated term",assumptions,result.term,result.type));
    const expected=this.checker.verify(this.term(d.expected,scope));
    if(!scope.equal(result.type,expected.type))
      throw Error(`The evaluated term has type ${cubicalText(result.type)}, but the expected value has type ${cubicalText(expected.type)}.`);
    const text=term=>{ const shown=cubicalText(term); return shown.length>200?`${shown.slice(0,200)}…`:shown; };
    if(!scope.equal(result.normal,expected.normal))
      throw Error(`The term evaluates to ${text(result.normal)}, not ${text(expected.normal)}.`);
    return text(result.normal);
  }
  translate(source, imported=new Map()) {
    const module=this.unit({source});
    const ast=parse(source),env=new Map(imported),declarations=[],directives=[];
    for(const d of ast.items??ast.declarations) {
      if(d.kind==="evaluate") {
        const line=source.slice(0,d.start).split("\n").length;
        try {
          directives.push({kind:"evaluate",name:`at line ${line}`,status:"checked",start:d.start,
            normalText:this.evaluate(d,new Scope(module,new Map(),env))});
        } catch(error) {
          directives.push({kind:"evaluate",name:`at line ${line}`,status:"not-translated",
            reason:error.message,start:d.start});
        }
        continue;
      }
      if(d.kind==="simp_rule"||d.kind==="simp_set") {
        try {
          if(d.kind==="simp_rule") {
            const rule=this.registeredSimpRule(d.rule,module,env,d.priority);
            const existing=this.simpRegistry.defaults.get(rule.identity);
            if(existing&&existing.origin===rule.origin)
              throw Error(`Simplification rule ${d.rule.text} is already registered in this module.`);
            if(!existing||rule.priority>existing.priority)this.simpRegistry.defaults.set(rule.identity,rule);
          } else {
            if(this.simpRegistry.sets.get(d.name.text)?.origin===this.moduleName)
              throw Error(`Simplification set ${d.name.text} is already declared in this module.`);
            const rules=d.rules.map(token=>this.registeredSimpRule(token,module,env,0));
            this.simpRegistry.sets.set(d.name.text,{origin:this.moduleName,
              rules:uniqueSimpRules(rules)});
          }
          directives.push({kind:d.kind,name:d.rule?.text??d.name.text,status:"checked",start:d.start});
        } catch(error) {
          directives.push({kind:d.kind,name:d.rule?.text??d.name.text,status:"not-translated",
            reason:error.message,start:d.start});
        }
        continue;
      }
      // Each declaration counts its own rewriting work.
      const unit=module.with({work:emptyRewriteWork()});
      this.onDeclarationStart?.(d);
      const previousHints=this.checker.kernel?.unfoldingHints;
      try {
        if(d.kind==="axiom") throw Error("Axiom declarations require an explicit assumption policy; not translated.");
        let expression=d.value;
        if(!expression) {
          expression={kind:"proof",type:d.type,statements:d.body};
          for(let j=d.params.length-1;j>=0;) {
            const group=d.params[j].group??j,members=[];
            while(j>=0&&(d.params[j].group??j)===group)members.unshift(d.params[j--]);
            expression=members.length===1
              ? {kind:"lambda",name:members[0].name,domain:members[0].type,body:expression}
              : {kind:"binderGroup",binderKind:"lambda",names:members.map(p=>p.name),
                domain:members[0].type,body:expression};
          }
        }
        const schema=this.schema(expression,env,unit);
        if(schema) {
          schema.binding=this.checker.bindingName?.(d.name.text)??d.name.text;
          schema.levels=[];
          env.set(d.name.text,schema);
          declarations.push({name:d.name.text,status:"not-translated",template:true,reason:"Universe schema: each concrete specialization is checked at its use; no single closed translation claimed."});
          declarations.at(-1).rewriteWork={...unit.work};
          this.onDeclaration?.(d,declarations.at(-1));
          continue;
        }
        const term=this.term(expression,new Scope(unit,new Map(),env));
        // Normal forms are optional inspection output, not a prerequisite for
        // checking a declaration whose Nat value may have millions of successors.
        const checked=this.normalize?this.checker.verify(term):this.checker.infer(term);
        const native=this.nativeCheck?.(checked.term,checked.type,[],{normalize:false})??checked.native;
        if(native&&!native.ok)throw Error(`Native cubical check rejected: ${native.error}`);
        if(d.computable) {
          const assumptions=native?.axioms??checked.native?.axioms??[];
          if(assumptions.length)throw Error(this.nonComputingMessage("This computable declaration",
            assumptions,checked.term,checked.type));
        }
        const definition=this.checker.define?.(d.name.text,checked.term,checked.type)??checked.term;
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
      } finally {
        if(previousHints)this.checker.kernel.setUnfoldingHints(previousHints);
      }
      declarations.at(-1).rewriteWork={...unit.work};
      this.onDeclaration?.(d,declarations.at(-1));
      // Diagnostic observers may reject a late result after cleanup. Such a
      // result must not remain available to subsequent declarations.
      if (declarations.at(-1).status === "not-translated")
        env.set(d.name.text,{tag:"Untranslated",name:d.name.text,binding:this.checker.bindingName?.(d.name.text)??d.name.text,reason:declarations.at(-1).reason});
    }
    return {declarations,env,directives,simpRegistry:this.simpRegistry,
      normalizationVisits:this.checker.steps};
  }
  // A registration names an already checked rule; it records no reference.
  registeredSimpRule(token,module,env,priority=0) {
    const scope=new Scope(module.with({references:null}),new Map(),env);
    const term=this.term({kind:"name",name:token.text,start:token.start,end:token.end},scope,null);
    simplificationRule(scope,term);
    return {term,identity:boundedStateKey(term,searchDeadline(),this.checker.kernel),origin:module.moduleName,priority,
      sourceName:token.text};
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
        selected.push({term,identity:boundedStateKey(term,searchDeadline(),this.checker.kernel),reverse:item.reverse,
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
          const deadline=searchDeadline();
          const identity=boundedStateKey(term,deadline,this.checker.kernel);
          simplificationRule(scope,term,false,[],null,deadline);
          excluded.add(identity);
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
    // so a freeze replay's premise work is the replay's.
    const solvePremise=(premise,owner,deadline,at)=>{
      if(activePremises.includes(owner)||activePremises.length>=2)return null;
      // The available rules depend on the rules already solving a premise.
      let key=null;
      try {
        key=`${[...activePremises,owner].map(ruleNumber).join(",")}:${
          boundedStateKey(premise,deadline,this.checker.kernel)}`;
      } catch(error) {
        // A premise too large to remember is still searched, just not cached.
        if(!(error instanceof SearchLimit))throw error;
      }
      if(key!==null&&premises.outcomes.has(key))return premises.outcomes.get(key);
      // Premise search is speculative. Running out of attempts means this
      // conditional rule does not fire, like any other unproved premise.
      if(premises.attempts>=PREMISE_ATTEMPT_LIMIT) {premises.exhausted=true;return null;}
      premises.attempts++;
      at.unit.work.premiseAttempts++;
      activePremises.push(owner);
      let outcome=null;
      try {
        const available=rules.filter(rule=>!activePremises.includes(rule.identity));
        const {transition}=this.simplifyEqualityGoal(new Goal(premise,at),available,deadline);
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
        // a premise leaves that premise unproved. The shared elapsed-time
        // limit and kernel cancellation still stop the whole simplification.
        if(!(error instanceof SearchLimit))throw error;
      } finally {activePremises.pop();}
      if(key!==null)premises.outcomes.set(key,outcome);
      return outcome;
    };
    // Compile the rules after elaborating every user-written rule term, so the
    // time limit covers this phase alone.
    const deadline=searchDeadline();
    rules=uniqueSimpRules(selected.filter(rule=>!excluded.has(rule.identity)))
      .map(rule=>{
        let compiled;
        try {compiled=simplificationRule(scope,rule.term,rule.reverse,witnesses,
          (premise,deadline,at)=>solvePremise(premise,rule.identity,deadline,at),deadline);}
        catch(error) {throw unit.locate(error,
          {start:rule.sourceStart,end:rule.sourceEnd});}
        const available=rule.sourceName&&env.get(rule.sourceName);
        let sourceText=rule.sourceText??null;
        if(!sourceText&&available) {
          try {
            if(boundedStateKey(available,deadline,this.checker.kernel)===rule.identity)
              sourceText=rule.sourceName;
          } catch(error) {
            // A large shadowing term only disables a source edit suggestion.
            if(!(error instanceof SearchLimit||error instanceof SearchTimeout))throw error;
          }
        }
        return {...compiled,identity:rule.identity,reverse:!!rule.reverse,
          sourceStart:rule.sourceStart,sourceEnd:rule.sourceEnd,
          sourceText,displayName:sourceText??(rule.origin&&rule.sourceName
            ? `${rule.origin}.${rule.sourceName}`:"a checked rule")};
      });
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
      const replayScope=scope.withUnit(unit.with({work:emptyRewriteWork()}));
      let valid=false;
      // An omitted rule can change a failed premise search and hence a later
      // rewrite choice. Replay must preserve the constructed proof as well as
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
  term(n,scope,expected=null) {
    const result=this.termBody(n,scope,expected);
    if(scope.unit.references) {
      const {env,unit}=scope;
      let site;
      if(n.kind==="call" && n.fn.kind==="name" && !env.has(n.fn.name)) site=n.fn;
      else if(n.kind==="name" && !env.has(n.name)) site=n;
      else if(n.kind==="binary" && ["=","->","and","or"].includes(n.operator))
        site={name:n.operator,start:n.operatorStart,end:n.operatorEnd};
      else if(["lambda","forall","exists","binderGroup"].includes(n.kind)&&!n.generatedBinder) {
        const binder=n.binderKind??n.kind;
        const name=binder==="lambda"?"fun":binder;
        if(unit.source.slice(n.start,n.start+name.length)===name)
          site={name,start:n.start,end:n.start+name.length};
      }
      if(Number.isInteger(site?.start)) this.reference(scope,{...site,expressionSite:true,
        role:"language expression",description:`Checked expression: ${unit.source.slice(n.start,n.end).trim()}`},
        result);
    }
    return result;
  }
  termBody(n,scope,expected=null) {
    scope.checkDeadline();
    if(!n) throw Error("Missing source expression.");
    const {env}=scope;
    const tr=(x,e=expected)=>this.term(x,scope,e);
    const inferred=t=>scope.infer(t);
    switch(n.kind) {
      case "withUnfolding": {
        if (!this.checker.scopedUnfolding) throw Error("Unfolding blocks require the native cubical backend.");
        const names=n.hints.map(hint=>{
          let value=env.get(hint.text);
          while(value?.tag==="App")value=value.fn;
          if(value?.tag!=="DefRef")throw Error(`No checked definition to unfold: ${hint.text}`);
          this.reference(scope,{...hint,name:hint.text},value,null);
          return value.name;
        });
        return this.checker.scopedUnfolding(names,()=>tr(n.body),scope.context,expected,
          scope.dimensions,scope.unit.names);
      }
      case "pathApply": {
        const path=tr(n.left,null);
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
        if(env.has(n.name)) {
          const value=env.get(n.name);
          if(value.tag==="Untranslated") {
            const error=Error(`Untranslated dependency: ${n.name}`);
            error.blockedBy=value.binding??value.name;
            throw error;
          }
          if(value.tag==="Dimension")throw Error("Interval coordinates can only be used in interval arguments.");
          if(value.tag==="UniverseSchema")throw Error(`Universe arguments required: ${n.name}`);
          this.reference(scope,n,value);
          return value;
        }
        if(/^U[0-9]+$/.test(n.name))return T.universe(Number(n.name.slice(1)));
        if(n.name==="succ") { const name=scope.fresh();return T.lam(name,T.nat,T.succ(T.variable(name))); }
        const builtin={Nat:T.nat,Unit:T.unit,tt:T.point,Void:T.void};
        if(builtin[n.name])return builtin[n.name];
        throw Error(`Untranslated name: ${n.name}`);
      }
      case "number": {let t=T.zero;for(let i=0;i<n.value;i++)t=T.succ(t);
        this.reference(scope,{...n,name:String(n.value)},t);return t;}
      case "binaryNumber": {
        const term=tr(binaryLiteralSyntax(n));
        this.reference(scope,{...n,name:`0b${n.digits}`},term);return term;
      }
      case "binderGroup": {
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
          names.push(name);
        }
        let body=this.term(n.body,inner,kind==="lambda"?bodyExpected:null);
        const constructor=kind==="lambda"?T.lam:kind==="forall"?T.pi:T.sigma;
        for(const name of names.reverse())body=constructor(name,domain,body);
        return body;
      }
      case "lambda": case "forall": case "exists": {
        let domain=n.domain?tr(n.domain,null):null;
        if(n.kind==="lambda"&&!domain) {
          if(!expected)throw Error("Untyped lambda requires an expected function type.");
          const pi=scope.nf(expected);
          if(pi.tag!=="Pi")throw Error("Untyped lambda requires an expected function type.");
          domain=pi.domain;
        }
        const name=scope.fresh(n.name.text);
        const inner=this.sourceBinding(n.name,T.variable(name),scope.bind(name,domain));
        let bodyExpected=null;
        if(n.kind==="lambda"&&expected) {
          const pi=scope.nf(expected);
          if(pi.tag==="Pi")bodyExpected=T.app(T.lam(pi.name,pi.domain,pi.body),T.variable(name));
        }
        const body=this.term(n.body,inner,bodyExpected);
        return (n.kind==="lambda"?T.lam:n.kind==="forall"?T.pi:T.sigma)(name,domain,body);
      }
      case "binary": {
        const left=tr(n.left,null);
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
        const builtin=n.fn.kind==="name"&&!env.has(n.fn.name)?n.fn.name:null;
        if(["ua","UnivalenceBeta"].includes(builtin)&&n.args.length>=3) {
          const [universe,A,B]=n.args.slice(0,3).map(a=>tr(a,null));
          if(universe.tag!=="U")throw Error("Univalence requires a concrete universe.");
          scope.check(A,universe);
          scope.check(B,universe);
          const build=(A,B)=>{
            const E=halfAdjointEquiv(A,B),en=scope.fresh("equivalence"),x=scope.fresh("argument");
            return builtin==="ua"?T.lam(en,E,publicUnivalencePath(A,B,T.variable(en),universe.level)):
              T.lam(en,E,T.lam(x,A,publicUnivalenceBeta(A,B,T.variable(en),T.variable(x))));
          };
          let fn;
          if(this.checker.specializeSchema && this.checker.kernel?.optimizations?.reuseChecks !== false) {
            // The computational derivation is generic in A and B. Check that
            // closed function once per universe, then check ordinary applications.
            const generic=this.checker.specializeSchema(`builtin__${builtin}`,[universe.level],()=>{
              const a=scope.fresh("sourceType"),b=scope.fresh("targetType");
              return T.lam(a,universe,T.lam(b,universe,build(T.variable(a),T.variable(b))));
            });
            fn=T.app(T.app(generic,A),B);
          } else fn=build(A,B);
          for(const arg of n.args.slice(3)) {
            const type=scope.nf(inferred(fn).type);
            if(type.tag!=="Pi")throw Error(`Too many arguments to ${builtin}.`);
            fn=T.app(fn,tr(arg,type.domain));
          }
          return fn;
        }
        if(["Truncate","TruncateIntro","TruncateProp","TruncateElim","LEM","Choice"].includes(builtin)) {
          if(!n.args.length)throw Error(`${builtin} needs a universe argument.`);
          const universe=tr(n.args[0],null);
          if(universe.tag!=="U"||!this.checker.assume)throw Error("Logical assumptions require a concrete universe and an explicit native context.");
          let fn=libraryAssumption(this.checker,builtin,universe.level,scope.context);
          for(const arg of n.args.slice(1)) {
            const type=scope.nf(inferred(fn).type);
            if(type.tag!=="Pi")throw Error(`Too many arguments to ${builtin}.`);
            fn=T.app(fn,tr(arg,type.domain));
          }
          return fn;
        }
        if(builtin==="typed"&&n.args.length===2) {
          const type=tr(n.args[0],null),term=tr(n.args[1],type);
          const checked=scope.check(term,type);
          return scope.ascribe(checked,type);
        }
        if(["path","PathP","comp","fill"].includes(builtin)) {
          const size=n.args.length;
          if((builtin==="path"&&size!==2)||(builtin==="PathP"&&size!==3)||(builtin==="comp"&&size<2)||(builtin==="fill"&&size<3))
            throw Error(`Invalid arguments to ${builtin}.`);
          const dim=scope.fresh("i"),family=this.dimensionBody(n.args[0],dim,scope);
          if(builtin==="path")return T.line(dim,family,this.dimensionBody(n.args[1],dim,scope,family));
          if(builtin==="PathP")return T.path(dim,family,tr(n.args[1],null),tr(n.args[2],null));
          const system=n.args.slice(builtin==="fill"?3:2).map(part=>{
            if(part.kind==="call"&&part.fn.kind==="name"&&part.fn.name==="face_when"&&part.args.length===2)
              return {face:this.cofibration(part.args[0],env),term:this.dimensionBody(part.args[1],dim,scope,family)};
            if(part.kind!=="call"||part.fn.kind!=="name"||part.fn.name!=="face"||part.args.length!==3)
              throw Error("A composition wall has syntax face(i, 0 or 1, fun (j : Interval) => ...).");
            const [coordinate,endpoint,wall]=part.args;
            if(coordinate.kind!=="name"||env.get(coordinate.name)?.tag!=="Dimension"||endpoint.kind!=="number"||![0,1].includes(endpoint.value))
              throw Error("A composition face needs an outer interval coordinate and endpoint 0 or 1.");
            return {face:F.endpoint(env.get(coordinate.name).name,endpoint.value),term:this.dimensionBody(wall,dim,scope,family)};
          });
          const base=tr(n.args[1],null);
          return builtin==="fill"?withNativeReferences([family,system,base],(family,system,base)=>fill(dim,family,system,base,this.interval(n.args[2],env))):T.comp(dim,family,system,base);
        }
        if(["path_from_transport","path_to_transport"].includes(builtin)&&n.args.length===4) {
          const dim=scope.fresh("i"),family=this.dimensionBody(n.args[0],dim,scope);
          const left=tr(n.args[1],null),right=tr(n.args[2],null),value=tr(n.args[3],null);
          return T.app((builtin==="path_from_transport"?transportToDependentPath:dependentPathToTransport)(dim,family,left,right),value);
        }
        if(builtin==="at"&&n.args.length===2)return T.at(tr(n.args[0],null),this.interval(n.args[1],env));
        if(builtin==="pushout_induction"&&n.args.length===5) {
          const [motive,left,right,bridge,value]=n.args.map(a=>tr(a,null));
          return T.app(T.pushElim(motive,left,right,bridge),value);
        }
        if(builtin==="Pushout"&&n.args.length===5) return pushout(...n.args.map(a=>tr(a,null)),
          {deadline:this.checker.kernel?.deadline||performance.now()+1000,
            checkDeadline:()=>this.checker.kernel?.checkDeadline()});
        if(["push_left","push_right"].includes(builtin)&&n.args.length===2)
          return (builtin==="push_left"?T.pushLeft:T.pushRight)(...n.args.map(a=>tr(a,null)));
        if(builtin==="push_path"&&n.args.length===2) {
          const [P,a]=n.args.map(a=>tr(a,null)),i=scope.fresh("push");
          return T.line(i,P,T.pushPath(P,a,I.variable(i)));
        }
        if(builtin==="pair_induction"&&n.args.length===3) {
          const [motive,branch,value]=n.args.map(a=>tr(a,null));
          const sigma=scope.nf(inferred(value).type);
          if(sigma.tag!=="Sigma")throw Error("pair_induction requires a dependent pair.");
          const x=scope.fresh(),y=scope.fresh(),first=T.variable(x),second=T.variable(y);
          const fiber=T.app(T.lam(sigma.name,sigma.domain,sigma.body),first);
          const branchType=T.pi(x,sigma.domain,T.pi(y,fiber,
            T.app(motive,T.pair(sigma,first,second))));
          scope.check(branch,branchType);
          // Cubical Sigma eta identifies (fst p, snd p) with p. The native
          // checker verifies the dependent result conversion at the motive.
          const result=T.app(T.app(branch,T.first(value)),T.second(value));
          const type=T.app(motive,value),checked=scope.check(result,type);
          return scope.ascribe(checked,type);
        }
        if(builtin==="succ"&&n.args.length===1)return T.succ(tr(n.args[0],T.nat));
        if(builtin==="W"&&n.args.length===2) {
          const domain=tr(n.args[0],null),family=tr(n.args[1],null),name=scope.fresh();
          return T.w(name,domain,T.app(family,T.variable(name)));
        }
        if(builtin==="sup"&&n.args.length===3) {
          const type=tr(n.args[0],null),shape=scope.nf(type);
          if(shape.tag!=="W")throw Error("sup requires a W type.");
          const label=tr(n.args[1],shape.domain),arity=T.app(T.lam(shape.name,shape.domain,shape.body),label);
          return T.sup(type,label,tr(n.args[2],T.pi(scope.fresh(),arity,type)));
        }
        if(builtin==="wrec"&&n.args.length===4) {
          const [type,motive,step,value]=n.args.map(a=>tr(a,null));
          scope.check(value,type);
          return T.wrec(motive,step,value);
        }
        if(builtin==="unit_induction"&&n.args.length===3) {
          const [motive,point,value]=n.args.map(a=>tr(a,null));
          return T.unitrec(motive,point,value);
        }
        if(builtin==="FunExt"&&n.args.length===6) {
          const [universe,A,B,f,g,h]=n.args.map(a=>tr(a,null));
          if(universe.tag!=="U")throw Error("FunExt needs a concrete universe.");
          scope.check(A,universe);
          const x=scope.fresh(),dim=scope.fresh("i"),variable=T.variable(x),fiber=T.app(B,variable);
          scope.check(B,T.pi(x,A,universe));
          const functionType=T.pi(x,A,fiber);
          scope.check(f,functionType);
          scope.check(g,functionType);
          const pointwise=T.pi(x,A,T.path(dim,fiber,T.app(f,variable),T.app(g,variable)));
          scope.check(h,pointwise);
          return T.line(dim,functionType,T.lam(x,A,T.at(T.app(h,variable),I.variable(dim))));
        }
        if(builtin==="absurd"&&n.args.length===1) {
          if(!expected)throw Error("absurd requires an expected type.");
          return T.abort(expected,tr(n.args[0],T.void));
        }
        if(["left","right"].includes(builtin)&&n.args.length===1) {
          if(!expected)throw Error("Sum injection requires an expected type.");
          const sum=scope.nf(expected);
          if(sum.tag!=="Sum")throw Error("Expected a sum type.");
          return (builtin==="left"?T.inl:T.inr)(expected,tr(n.args[0],sum[builtin]));
        }
        if(builtin==="refl"&&n.args.length===1) {
          const value=tr(n.args[0],null);return T.line(scope.fresh("i"),inferred(value).type,value);
        }
        if(builtin==="sym"&&n.args.length===1) {
          const p=tr(n.args[0],null),type=scope.nf(inferred(p).type);
          if(type.tag!=="Path")throw Error("sym requires a path.");
          // A constant path is its own reversal. Retain the ordinary path
          // term so applying it to a large interval need not distribute the
          // reversal inside the native checker.
          if(p.tag==="PLam"&&!freeDimensions(p.body).has(p.dim)
            &&!freeDimensions(p.family).has(p.dim))return p;
          // Cubist equality has a constant carrier (dependent Path reversal
          // is checked by the core directly, rather than silently approximated).
          const i=scope.fresh("i"),result=T.line(i,type.family,T.at(p,I.reverse(I.variable(i))));
          return this.checker.ascribe && this.checker.kernel?.optimizations?.compactPaths !== false ? scope.ascribe(result,T.path(i,type.family,type.right,type.left)) : result;
        }
        if(builtin==="trans"&&n.args.length===2) {
          const p=tr(n.args[0],null),q=tr(n.args[1],null),pt=scope.nf(inferred(p).type),qt=scope.nf(inferred(q).type);
          if(pt.tag!=="Path"||qt.tag!=="Path")throw Error("trans requires paths.");
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
        if(builtin==="cong"&&n.args.length===2) {
          const fn=tr(n.args[0],null),p=tr(n.args[1],null),pt=scope.nf(inferred(p).type);
          if(pt.tag!=="Path")throw Error("cong requires a path.");
          const left=T.app(fn,pt.left),type=inferred(left).type,i=scope.fresh("i");
          const result=T.line(i,type,T.app(fn,T.at(p,I.variable(i))));
          return this.checker.ascribe && this.checker.kernel?.optimizations?.compactPaths !== false ? scope.ascribe(result,T.path(i,type,left,T.app(fn,pt.right))) : result;
        }
        if(builtin==="apd"&&n.args.length===4) {
          const [fn,x,y,p]=n.args.map(a=>tr(a,null));
          const pt=scope.nf(inferred(p).type),ft=scope.nf(inferred(fn).type);
          if(pt.tag!=="Path"||ft.tag!=="Pi"||!scope.equal(pt.left,x)||!scope.equal(pt.right,y))
            throw Error("Dependent action needs a function and a path with the supplied endpoints.");
          const i=scope.fresh("i"),family=T.app(T.lam(ft.name,ft.domain,ft.body),T.at(p,I.variable(i)));
          const action=T.line(i,family,T.app(fn,T.at(p,I.variable(i))));
          return T.app(dependentPathToTransport(i,family,T.app(fn,x),T.app(fn,y)),action);
        }
        if(builtin==="apd_path"&&n.args.length===2) {
          const fn=tr(n.args[0],null),p=tr(n.args[1],null);
          const ft=scope.nf(inferred(fn).type),pt=scope.nf(inferred(p).type);
          if(ft.tag!=="Pi"||pt.tag!=="Path"||freeDimensions(pt.family).has(pt.dim))
            throw Error("apd_path needs a dependent function and a homogeneous path.");
          scope.expect(pt.family,ft.domain);
          const dim=scope.fresh("i"),index=T.at(p,I.variable(dim));
          const family=T.app(T.lam(ft.name,ft.domain,ft.body),index);
          return T.line(dim,family,T.app(fn,index));
        }
        if(builtin==="transport"&&n.args.length===5) {
          const [family,x,y,p,value]=n.args.map(a=>tr(a,null));
          const pt=scope.nf(inferred(p).type);if(pt.tag!=="Path")throw Error("transport requires a path.");
          if(!scope.equal(pt.left,x)||!scope.equal(pt.right,y))throw Error("Transport endpoints do not match.");
          const i=scope.fresh("i");return T.comp(i,T.app(family,T.at(p,I.variable(i))),[],value);
        }
        if(builtin==="path_induction"&&n.args.length===6) {
          const [A,C,d,x,y,p]=n.args.map(a=>tr(a,null)),i=scope.fresh("i"),j=scope.fresh("j");
          const pt=scope.nf(inferred(p).type);
          if(pt.tag!=="Path"||!scope.equal(pt.family,A)||!scope.equal(pt.left,x)||!scope.equal(pt.right,y))throw Error("Path induction endpoints/carrier do not match.");
          const segment=T.line(j,A,T.at(p,I.meet(I.variable(i),I.variable(j))));
          const family=T.app(T.app(T.app(C,x),T.at(p,I.variable(i))),segment);
          return T.comp(i,family,[],T.app(d,x));
        }
        if(builtin==="based_induction"&&n.args.length===8) {
          const [universe,motiveUniverse,A,x,C,d,y,p]=n.args.map(a=>tr(a,null));
          if(universe.tag!=="U"||motiveUniverse.tag!=="U")throw Error("Based induction needs concrete universes.");
          scope.check(A,universe);
          const b=scope.fresh(),q=scope.fresh(),i=scope.fresh("i"),j=scope.fresh("j");
          const pathType=T.path(j,A,x,T.variable(b));
          scope.check(C,T.pi(b,A,T.pi(q,pathType,motiveUniverse)));
          scope.check(p,T.path(j,A,x,y));
          const reflexivity=T.line(j,A,x);
          scope.check(d,T.app(T.app(C,x),reflexivity));
          const segment=T.line(j,A,T.at(p,I.meet(I.variable(i),I.variable(j))));
          return T.comp(i,T.app(T.app(C,T.at(p,I.variable(i))),segment),[],d);
        }
        let fn=n.fn.kind==="name"&&env.get(n.fn.name)?.tag==="UniverseSchema"?env.get(n.fn.name):tr(n.fn,null);
        for(const arg of n.args) {
          if(fn.tag==="UniverseSchema") {
            const universe=tr(arg,null);if(universe.tag!=="U")throw Error("Schema requires a concrete universe level.");
            const templateEnv=new Map(fn.env).set(fn.parameter,universe);
            const next=this.schema(fn.body,templateEnv,fn),
              levels=[...(fn.levels??[]),universe.level];
            if(next) { next.binding=fn.binding;next.levels=levels;fn=next; }
            else {
              const schema=fn;
              // The schema body belongs to its definition's source unit, not
              // this call site: do not attach its offsets to the caller's file.
              // Only binder names are collected; no edit applies to a
              // specialization. Its search work counts as the caller's.
              const sourceNames=new Map();
              const unit=scope.unit.with({simpRegistry:copySimpRegistry(schema.simpRegistry),
                moduleName:schema.moduleName,source:schema.source,freezeSuggestions:false,
                references:(node,term)=>{
                  if(node.isBinding&&term.tag==="Var")sourceNames.set(term.name,node.name);
                }});
              try {
                fn=this.checker.specializeSchema&&schema.binding
                  ?this.checker.specializeSchema(schema.binding,levels,()=>this.term(schema.body,
                    new Scope(unit,new Map(),templateEnv),null))
                  :this.term(schema.body,scope.withUnit(unit).withEnv(templateEnv),null);
              } catch(error) {
                // The failed body uses offsets in the defining module. Report
                // that origin in the message and select the caller's token.
                unit.locate(error,schema.body);
                const prefix=`${schema.moduleName}__`;
                const definition=schema.binding?.startsWith(prefix)
                  ?schema.binding.slice(prefix.length):schema.binding??'definition';
                error.message=`In template ${schema.moduleName}.${definition}: ${error.message}`;
                error.offset=n.fn.start??n.start;
                error.sourceEnd=n.fn.end??n.end;
                throw error;
              }
              if(sourceNames.size)this.checker.schemaSourceNames?.set(
                `${schema.binding}__${levels.map(level=>`U${level}`).join("_")}`,sourceNames);
              if(n.fn.kind==="name")this.reference(scope,{...n.fn,
                schemaBinding:schema.binding, universes:levels, role:"universe specialization",
                description:`Checked specialization ${n.fn.name}(${levels.map(level=>`U${level}`).join(", ")}) of a library universe template. View source opens the generic definition.`
              },fn);
            }
            continue;
          }
          const pi=scope.nf(inferred(fn).type);if(pi.tag!=="Pi")throw Error("Source application is not a function.");
          fn=T.app(fn,tr(arg,pi.domain));
        }
        if(fn.tag==="UniverseSchema")throw Error("Missing universe arguments.");
        return fn;
      }
      case "induction": {
        const value=tr(n.value,T.nat),k=scope.fresh(),ih=scope.fresh();
        const stepScope=this.sourceBinding(n.index,T.variable(k),scope.bind(k,T.nat));
        const motiveBody=this.term(n.type,stepScope,null),motive=T.lam(k,T.nat,motiveBody);
        const zero=tr(n.base,T.app(motive,T.zero));
        const hypothesisScope=this.sourceBinding(n.hypothesis,T.variable(ih),stepScope.bind(ih,motiveBody));
        const step=T.lam(k,T.nat,T.lam(ih,motiveBody,this.term(n.step,hypothesisScope,T.app(motive,T.succ(T.variable(k))))));
        return T.natrec(motive,zero,step,value);
      }
      case "match": {
        const value=tr(n.value,null),type=inferred(value).type,sum=scope.nf(type);
        if(sum.tag!=="Sum")throw Error("match requires a sum type.");
        const name=scope.fresh(),inner=scope.bind(name,type);
        const motive=T.lam(name,type,this.term(n.type,
          n.motiveName?inner.alias(n.motiveName.text,T.variable(name)):inner,null));
        const branch=side=>{
          const local=scope.fresh(),domain=sum[side],variable=T.variable(local);
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
    try {return this.blockBody(statements,goal);}
    catch(error) {
      throw goal.scope.unit.locate(error,statements[0]);
    }
  }
  // A statement makes a transition from the goal (proof-goals.mjs), and the
  // statements after it prove the goal that remains.
  blockBody(statements,goal) {
    if(!statements.length)throw Error("Proof block has no conclusion.");
    const [first,...rest]=statements;
    const {scope}=goal,{unit,env}=scope;
    if(first.kind==="exact") {
      if(rest.length)throw Error("Statements after exact are unreachable.");
      return this.term(first.value,scope,goal.target);
    }
    if(first.kind==="rfl") {
      if(rest.length)throw Error("Statements after rfl are unreachable.");
      const path=goal.equality();
      if(!path)throw Error("rfl requires a homogeneous equality goal.");
      return reflexivity(goal,path);
    }
    if(first.kind==="calc") {
      if(rest.length)throw Error("Statements after calc are unreachable.");
      const path=goal.equality();
      if(!path)throw Error("calc requires a homogeneous equality goal.");
      if(!first.steps.length)throw Error("calc requires at least one step.");
      // calc does no search: each step's proof is ordinary elaboration, and
      // composing the checked steps is bounded by their number.
      let previous=path.left,proof=null;
      for(const [index,step] of first.steps.entries()) {
        scope.checkDeadline();
        const left=step.left.kind==="name"&&step.left.name==="_"?previous:this.term(step.left,scope,path.family);
        if(!scope.equal(left,previous))throw Error("calc step left endpoint does not match the preceding endpoint.");
        const right=this.term(step.right,scope,path.family);
        const target=T.path(scope.fresh("i"),path.family,left,right);
        const raw=step.proof.kind==="block"?this.block(step.proof.body,goal.with(target))
          :this.term(step.proof.value,scope,target);
        const checked=scope.check(raw,target);
        const witness=scope.ascribe(checked,target);
        // The step's `by` keyword links to its checked path.
        this.reference(scope,{...step,start:step.by?.start??step.start,end:step.by?.end??step.end,
          name:`calc step ${index+1}`,role:"calculation step",expansionIndex:index+1,
          description:`Checked equality step ${index+1} of ${first.steps.length}.`},
          witness);
        proof=proof?composePaths(scope,proof,witness):witness;
        previous=right;
      }
      if(!scope.equal(previous,path.right))throw Error("calc final endpoint does not match the goal.");
      scope.check(proof,goal.target);
      this.recordTactic(first,scope,proof,{role:"calculation witness",
        description:`Checked ${first.steps.length}-step equality chain.`});
      return proof;
    }
    if(first.kind==="rw") {
      let transition=new Transition(goal);
      for(const item of first.rules) {
        try {transition=this.rewriteGoal(transition,first,item);}
        catch(error) {throw unit.locate(error,item);}
      }
      const proof=this.remaining(rest,transition.next,
        ()=>Error("rw left an unresolved equality goal; add a following proof statement."));
      return this.conclude(first,transition,proof,()=>({role:"rewrite witness",
        description:`Checked rewrite using ${first.rules.map(item=>
          unit.source.slice(item.value.start,item.value.end)).join(", ")}.`}));
    }
    if(first.kind==="simpOnly") {
      const rules=this.selectedSimpRules(first.rules,scope,first.only,first.without,first.witnesses);
      if(first.at) {
        if(!rest.length)throw Error("A simplified hypothesis copy must be followed by a proof statement.");
        const source=env.get(first.at.text);
        if(!source||!this.localSources.has(source))
          throw Error(`simp at requires a local hypothesis: ${first.at.text}.`);
        // The hypothesis's statement is simplified and its proof carried forward.
        const hypothesis=goal.with(scope.infer(source).type);
        const {transition}=this.simplifyEqualityGoal(hypothesis,rules);
        const simplified=transition.next.target;
        const checked=scope.check(transition.forward(source),simplified);
        const named=scope.ascribe(checked,simplified);
        const final=this.block(rest,goal.at(this.sourceBinding(first.as,named,scope)));
        if(unit.references)this.recordTactic(first,scope,named,{role:"simplification witness",
          freeze:this.freezeSimplification(first,rules,transition.trace,scope,(subset,at)=>{
            const replay=this.simplifyEqualityGoal(hypothesis.at(at),subset).transition;
            return at.equal(replay.next.target,simplified)&&at.equal(replay.forward(source),named);
          }),
          description:`Checked simplified hypothesis copy with ${transition.trace.length} rewrites.`},
          transition.trace.map(step=>({...step,phase:"hypothesis"})));
        return final;
      }
      if(scope.nf(goal.target).tag!=="Path") {
        const {transition}=this.simplifyTypeTerm(goal,rules);
        if(!rest.length)throw Error("simp left a type goal; add a following proof statement.");
        const proof=this.block(rest,transition.next);
        return this.conclude(first,transition,proof,result=>({role:"simplification witness",
          freeze:this.freezeSimplification(first,rules,transition.trace,scope,(subset,at)=>{
            const replay=this.simplifyTypeTerm(goal.at(at),subset).transition;
            return at.equal(replay.next.target,transition.next.target)&&at.equal(replay.rebuild(proof),result);
          }),
          description:`Checked type simplification with ${transition.trace.length} rewrites.`}),
          transition.trace.map(step=>({...step,phase:"goal"})));
      }
      const {transition,failures,dependent}=this.simplifyEqualityGoal(goal,rules);
      const proof=this.remaining(rest,transition.next,()=>{
        const blocked=failures[0];
        const detail=(blocked ? ` Rule ${blocked.rule.displayName} has an unproved premise at parameter ${blocked.parameter}; supply a local witness with simp with [name].${
          rules.premiseSearchExhausted?` Premise search stopped after ${PREMISE_ATTEMPT_LIMIT} attempts.`:""}` : "")
          +(dependent?dependentNote:"");
        const error=Error(`simp only left an unresolved equality goal; add a following proof statement.${detail}`);
        return unit.locate(error,blocked?.rule.sourceStart===undefined?first:
          {start:blocked.rule.sourceStart,end:blocked.rule.sourceEnd});
      });
      return this.conclude(first,transition,proof,result=>({role:"simplification witness",
        freeze:this.freezeSimplification(first,rules,transition.trace,scope,(subset,at)=>{
          const replay=this.simplifyEqualityGoal(goal.at(at),subset).transition;
          return at.equal(replay.next.target,transition.next.target)&&at.equal(replay.rebuild(proof),result);
        }),
        description:`Checked simplification with ${transition.trace.length} rewrites using ${[
          ...new Set(transition.trace.map(step=>step.rule.displayName))].join(", ")||"no theorem rules"}.`}),
        transition.trace);
    }
    if(first.kind==="simpaOnly") {
      if(rest.length)throw Error("Statements after simpa are unreachable.");
      const rules=this.selectedSimpRules(first.rules,scope,first.only,first.without,first.witnesses);
      const value=this.term(first.using,scope,null);
      const suppliedType=scope.infer(value).type;
      // One search limit for both simplifications; the supplied term was
      // elaborated before it starts.
      const deadline=searchDeadline();
      // A type is simplified as a whole and transported along; an equality at
      // its endpoints.
      const types=scope.nf(goal.target).tag!=="Path";
      const simplify=(subject,subset,limit)=>types
        ? this.simplifyTypeTerm(subject,subset,limit) : this.simplifyEqualityGoal(subject,subset,limit);
      const supplied=simplify(goal.with(suppliedType),rules,deadline);
      const target=simplify(goal,rules,deadline);
      const checked=this.checkSimplified(supplied.transition.forward(value),target.transition.next.target,
        scope,supplied.dependent||target.dependent);
      const trace=[...supplied.transition.trace.map(step=>({...step,phase:types?"supplied":"supplied type"})),
        ...target.transition.trace.map(step=>({...step,phase:"goal"}))];
      return this.conclude(first,target.transition,checked,result=>({role:"simplification witness",
        freeze:this.freezeSimplification(first,rules,trace,scope,(subset,at)=>{
          const replaySupplied=simplify(new Goal(suppliedType,at),subset).transition;
          const replayTarget=simplify(goal.at(at),subset).transition;
          if(!at.equal(replaySupplied.next.target,supplied.transition.next.target)
            ||!at.equal(replayTarget.next.target,target.transition.next.target))return false;
          const replayChecked=at.check(replaySupplied.forward(value),replayTarget.next.target);
          return at.equal(replayTarget.rebuild(replayChecked),result);
        }),
        description:`Checked ${types?"type ":""}simpa with ${trace.length} rewrites using ${[
          ...new Set(trace.map(step=>step.rule.displayName))].join(", ")||"no theorem rules"}.`}),
        trace);
    }
    if(first.kind==="intro") {
      const pi=scope.nf(goal.target);
      if(pi.tag!=="Pi")throw Error("intro requires a dependent function goal.");
      const name=scope.fresh(first.name.text),variable=T.variable(name);
      const inner=this.sourceBinding(first.name,variable,scope.bind(name,pi.domain));
      const next=new Goal(T.app(T.lam(pi.name,pi.domain,pi.body),variable),inner);
      return new Transition(goal,next,[steps.abstraction(name,pi.domain)]).rebuild(this.block(rest,next));
    }
    if(first.kind==="ext") {
      const path=goal.equality();
      if(!path)throw Error("ext requires equality of functions with a fixed type.");
      const pi=scope.nf(path.family);
      if(pi.tag!=="Pi")throw Error("ext requires equality of functions.");
      const name=scope.fresh(first.variable.text),variable=T.variable(name);
      const inner=this.sourceBinding(first.variable,variable,scope.bind(name,pi.domain));
      const output=T.app(T.lam(pi.name,pi.domain,pi.body),variable);
      const next=new Goal(T.path(scope.fresh("i"),output,T.app(path.left,variable),T.app(path.right,variable)),inner);
      return new Transition(goal,next,[steps.congruence(name,pi.domain,path.family)]).rebuild(this.block(rest,next));
    }
    if(first.kind==="over") {
      if(rest.length)throw Error("Statements after over are unreachable.");
      const target=scope.nf(goal.target);
      if(target.tag!=="Path")throw Error("over requires an expected PathP goal.");
      const C=this.term(first.family,scope,null),p=this.term(first.path,scope,null);
      const base=scope.nf(scope.infer(p).type);
      if(base.tag!=="Path"||freeDimensions(base.family).has(base.dim))
        throw Error("over requires a homogeneous base path.");
      const dim=scope.fresh("i"),family=T.app(C,T.at(p,I.variable(dim)));
      const transported=T.comp(dim,family,[],target.left);
      const fiber=T.app(C,base.right);
      const next=goal.with(T.path(scope.fresh("j"),fiber,transported,target.right));
      const transition=new Transition(goal,next,
        [steps.lemma(transportToDependentPath(dim,family,target.left,target.right),next.target)]);
      const result=transition.rebuild(this.block(first.body,next));
      scope.check(result,goal.target);
      return result;
    }
    if(first.kind==="let"&&first.target.kind==="name") {
      const value=this.term(first.value,scope,null);
      scope.infer(value);
      return this.block(rest,goal.at(this.sourceBinding(first.target,value,scope)));
    }
    if(first.kind==="obtain") {
      const value=this.term(first.value,scope,null);
      let inner=scope;
      const bind=(pattern,term)=>{
        if(pattern.kind==="name") {inner=this.sourceBinding(pattern,term,inner);return;}
        if(pattern.kind!=="pair"||scope.nf(scope.infer(term).type).tag!=="Sigma")
          throw Error("obtain requires a dependent pair matching its pattern.");
        bind(pattern.left,T.first(term));bind(pattern.right,T.second(term));
      };
      scope.infer(value);bind(first.target,value);
      return this.block(rest,goal.at(inner));
    }
    if(first.kind==="cases") {
      if(rest.length)throw Error("Statements after cases are not yet translated.");
      const value=this.term(first.value,scope,null),type=scope.infer(value).type;
      const sum=scope.nf(type);
      if(sum.tag!=="Sum")throw Error("cases requires a sum type.");
      const motive=T.lam(scope.fresh(),type,goal.target);
      const branch=side=>{
        const name=scope.fresh(),domain=sum[side];
        const inner=this.sourceBinding(first[side],T.variable(name),scope.bind(name,domain));
        return T.lam(name,domain,this.block(first[side+"Body"],goal.at(inner)));
      };
      return T.sumrec(motive,branch("left"),branch("right"),value);
    }
    if(first.kind==="have") {
      const type=this.term(first.type,scope,null),value=this.block(first.body,new Goal(type,scope));
      const checked=scope.check(value,type);
      // A local lemma keeps its declared signature just like a top-level proof.
      const named=scope.ascribe(checked,type);
      return this.block(rest,goal.at(this.sourceBinding(first.name,named,scope)));
    }
    if(first.kind==="haveValue") {
      const type=first.type?this.term(first.type,scope,null):null;
      const value=this.term(first.value,scope,type);
      const checked=type?scope.check(value,type):scope.infer(value).term;
      const signature=type??scope.infer(checked).type;
      const named=scope.ascribe(checked,signature);
      return this.block(rest,goal.at(this.sourceBinding(first.name,named,scope)));
    }
    throw Error(`Proof tactic not yet translated: ${first.kind}`);
  }
  // One rw rule: rewrite its selected occurrence in the remaining goal.
  rewriteGoal(transition,first,item) {
    const {scope}=transition.goal,path=transition.next.equality();
    if(!path)throw Error("rw requires a homogeneous equality goal.");
    const rule=equalityRule(scope,this.term(item.value,scope,null),item.reverse);
    // The time limit covers this rule's search only: not elaborating the
    // rule, the statements after rw, or rebuilding the proof afterwards.
    const deadline=searchDeadline();
    let target=first.target,changed;
    if(target) changed=rewriteFirst(scope,path[target==="lhs"?"left":"right"],path.family,rule,first.occurrence,"preorder",deadline);
    else {
      // Count eligible occurrences through the left endpoint, then the right.
      const left=findRewrite(scope,path.left,path.family,rule,first.occurrence,"preorder",deadline);
      if(left.found) {changed=left.found;target="lhs";}
      else {
        const right=findRewrite(scope,path.right,path.family,rule,
          first.occurrence-left.eligible,"preorder",deadline);
        if(!right.found)throw Error(left.unsupported||right.unsupported
          ? "Rewrite match occurs in an unsupported dependent position."
          : `Rewrite occurrence ${first.occurrence} was not found (${left.eligible+right.eligible} eligible matches).`);
        changed=right.found;target="rhs";
      }
    }
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
    const keyword=tacticKeywords[first.kind];
    this.reference(scope,{...first,name:keyword,end:first.start+keyword.length,...details},proof);
    for(const [index,step] of trace.entries()) {
      const rule=step.rule.displayName;
      this.reference(scope,{name:`simp step ${index+1}`,start:first.start,
        end:first.start+keyword.length,
        role:"simplification step",expansionIndex:index+1,
        traceParent:first.start,
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
  findSimplification(root,carrier,rules,scope,deadline) {
    try {return findRewrite(scope,root,carrier,rules,1,"postorder",deadline);}
    catch(error) {
      const rule=error.rewriteRule;
      throw scope.unit.locate(error,rule?.sourceStart===undefined?null:
        {start:rule.sourceStart,end:rule.sourceEnd});
    }
  }
  // Simplify a type goal as a whole. Its plan transports along the composite
  // of the rewrites' paths of types.
  simplifyTypeTerm(goal,rules,deadline=searchDeadline()) {
    const {scope}=goal;
    const carrier=scope.nf(scope.infer(goal.target).type);
    if(carrier.tag!=="U")throw Error("General simplification requires a type-valued goal.");
    let current=goal.target,dependent=false;
    const trace=[],states=new Set();
    while(true) {
      scope.checkDeadline();
      if(performance.now()>deadline)throw new SearchTimeout("Simplification elapsed-work budget exceeded.");
      const state=boundedStateKey(current,deadline,this.checker.kernel);
      if(states.has(state))throw new SearchLimit("Simplification cycle detected in the selected rules.");
      states.add(state);
      // A match in a dependent position is skipped, not an error.
      const {found,unsupported}=this.findSimplification(current,carrier,rules,scope,deadline);
      dependent=unsupported;
      if(!found)break;
      if(trace.length>=64)throw new SearchLimit("Simplification rewrite budget exceeded.");
      current=found.after;
      trace.push({side:"type",rule:found.rule,witness:found.witness,visits:found.visits,
        premiseRules:found.premiseRules});
    }
    // Compose after the search, outside its time limit.
    let witness=null;
    for(const step of trace)witness=witness?composePaths(scope,witness,step.witness):step.witness;
    return {transition:new Transition(goal,goal.with(current),witness?[steps.transport(witness)]:[],trace),
      dependent};
  }
  // Simplify an equality goal at its endpoints. Each rewrite is one
  // composition step of the plan.
  simplifyEqualityGoal(goal,rules,deadline=searchDeadline()) {
    const {scope}=goal;
    let transition=new Transition(goal),dependent=false,failures=[];
    const states=new Set();
    while(true) {
      scope.checkDeadline();
      if(performance.now()>deadline)throw new SearchTimeout("Simplification elapsed-work budget exceeded.");
      const path=transition.next.equality();
      if(!path)throw Error("simp only requires a homogeneous equality goal.");
      const state=boundedStateKey([path.left,path.right],deadline,this.checker.kernel);
      if(states.has(state))throw new SearchLimit("Simplification cycle detected in the selected rules.");
      states.add(state);
      for(const rule of rules)rule.clearDiagnostic?.();
      let selected=null;
      dependent=false;
      for(const side of ["lhs","rhs"]) {
        // A match in a dependent position is skipped: the other endpoint, and
        // a goal that already holds by conversion, remain available.
        const {found,unsupported}=this.findSimplification(side==="lhs"?path.left:path.right,
          path.family,rules,scope,deadline);
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
      const {side,result}=selected;
      const next=T.path(scope.fresh("i"),path.family,
        side==="lhs"?result.after:path.left,
        side==="rhs"?result.after:path.right);
      // Rebuilding composes checked paths after the search, possibly after
      // later statements, and carries no search time limit.
      transition=transition.extend(steps.composition(scope,side,result.witness),goal.with(next),
        {side,rule:result.rule,witness:result.witness,visits:result.visits,premiseRules:result.premiseRules});
    }
    // `dependent` describes the final pass: a remaining match was skipped.
    return {transition,failures,dependent};
  }
}
