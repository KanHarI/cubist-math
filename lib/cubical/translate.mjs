import {withNativeReferences} from "./equivalence.mjs";
import {halfAdjointEquiv,publicUnivalencePath,publicUnivalenceBeta} from "./public-equivalence.mjs";
import {libraryAssumption} from "../../web/cubical-assumptions.mjs";
// Partial source translator. Unsupported syntax/foundations are explicit errors;
// no fallback axiom, old-kernel handle, or unchecked term enters this checker.
import {parse} from "../../web/mathscript/parser.mjs";
import {binaryLiteralSyntax} from "../../web/mathscript/binary-literals.mjs";
import {Checker,T,fill,substituteDimension} from "./core.mjs";
import {interval as I,face as F} from "./lattice.mjs";
import {freeDimensions} from "./dimension-slots.mjs";
import {pathConcat} from "./path-algebra.mjs";
import {equalityRule,simplificationRule,rewriteFirst} from "./proof-rewrite.mjs";
import {copySimpRegistry,orderedDefaultRules,resolveSimpSet,uniqueSimpRules} from "./simp-registry.mjs";
import {dependentPathToTransport,transportToDependentPath} from "./path-over.mjs";
import {pushout} from "./pushouts.mjs";

const emptyRewriteWork = () => ({
  traversals:0,candidateVisits:0,eligibleMatches:0,successfulRewrites:0,
  premiseAttempts:0,premiseProofs:0,premiseRewriteSteps:0,
});

export class Translator {
  constructor({normalize=true,nativeCheck=null,checker=new Checker(),onReference=null,onDeclaration=null,onDeclarationStart=null,
    simpRegistry,moduleName="source"}={}) {
    this.checker=checker;this.serial=0;
    this.normalize=normalize;this.nativeCheck=nativeCheck;
    this.dimensions=new Map();
    this.localSources=new WeakMap();
    this.onReference=onReference ? (node,term,context,env)=>onReference(node,term,context,new Map(this.dimensions),
      [...(env??[])].flatMap(([name,value])=>{
        const source=this.localSources.get(value);
        return source?.name===name ? [{...source,term:value}] : [];
      })) : null;
    this.onDeclaration=onDeclaration;
    this.onDeclarationStart=onDeclarationStart;
    this.simpRegistry=copySimpRegistry(simpRegistry);
    this.moduleName=moduleName;
    this.rewriteWork=emptyRewriteWork();
  }
  sourceBinding(node,term,context,env) {
    const name=node.text??node.name;
    // A source alias gets its own syntax object, even for `let y = x`.
    // This keeps lexical labels from overwriting x or leaking into siblings.
    term={...term};env.set(name,term);
    this.localSources.set(term,{name,start:node.start,end:node.end});
    this.onReference?.({...node,name,isBinding:true},term,new Map(context),env);
  }
  fresh(prefix="b") {let name;do{name=`${prefix}${++this.serial}`;}while(this.checker.assumptions?.has(name));return name;}
  locateProofError(error,node) {
    if(Number.isInteger(error.offset)||!Number.isInteger(node?.start))return error;
    error.offset=node.start;
    error.sourceEnd=node.end;
    const before=this.source.slice(0,error.offset);
    const line=before.split("\n").length;
    const column=error.offset-(before.lastIndexOf("\n")+1)+1;
    error.message+=` at ${line}:${column}`;
    return error;
  }
  // Interval names are cubical coordinates, never terms of a fabricated type.
  interval(n,env) {
    if(n.kind==="number"&&(n.value===0||n.value===1))return n.value===0?I.zero:I.one;
    if(n.kind==="name"&&env.get(n.name)?.tag==="Dimension")return I.variable(env.get(n.name).name);
    if(n.kind==="call"&&n.fn.kind==="name") {
      const args=n.args.map(a=>this.interval(a,env));
      if(n.fn.name==="flip"&&args.length===1)return I.reverse(args[0]);
      if(n.fn.name==="meet"&&args.length===2)return I.meet(...args);
      if(n.fn.name==="join"&&args.length===2)return I.join(...args);
    }
    throw Error("Expected an interval coordinate, 0, 1, flip, meet or join.");
  }
  cofibration(n,env) {
    if(n.kind==="number"&&(n.value===0||n.value===1))return n.value===0?F.bottom:F.top;
    if(n.kind==="binary"&&["and","or"].includes(n.operator))return (n.operator==="and"?F.meet:F.join)(this.cofibration(n.left,env),this.cofibration(n.right,env));
    if(n.kind==="call"&&n.fn.kind==="name"&&n.fn.name==="on"&&n.args.length===2) {
      const endpoint=n.args[1];
      if(endpoint.kind==="number"&&[0,1].includes(endpoint.value))return F.equalEndpoint(this.interval(n.args[0],env),endpoint.value);
    }
    throw Error("Expected a face formula: on(i, 0 or 1), and/or, 0 or 1.");
  }
  dimensionBody(n,dim,ctx,env,expected=null) {
    if(n.kind!=="lambda"||n.domain.kind!=="name"||n.domain.name!=="Interval")
      throw Error("Expected fun (i : Interval) => ... in a cubical binder.");
    const previous=this.dimensions,checkerDimensions=this.checker.dimensions;
    let index=0;while([...previous.values()].includes(index))index++;
    if(index>=64)throw Error("At most 64 simultaneous cubical dimensions are supported.");
    this.dimensions=new Map(previous).set(dim,index);this.checker.dimensions=this.dimensions;
    try {return this.term(n.body,ctx,new Map(env).set(n.name.text,{tag:"Dimension",name:dim}),expected);}
    finally {this.dimensions=previous;this.checker.dimensions=checkerDimensions;}
  }
  schema(expression,env,simpRegistry=this.simpRegistry,moduleName=this.moduleName) {
    return expression.kind==="lambda"&&expression.domain.kind==="name"&&expression.domain.name==="Universe"
      ? {tag:"UniverseSchema",parameter:expression.name.text,body:expression.body,
        env:new Map(env),simpRegistry:copySimpRegistry(simpRegistry),moduleName} : null;
  }
  translate(source, imported=new Map()) {
    this.source=source;
    const ast=parse(source),env=new Map(imported),declarations=[],directives=[];
    for(const d of ast.items??ast.declarations) {
      if(d.kind==="simp_rule"||d.kind==="simp_set") {
        try {
          if(d.kind==="simp_rule") {
            const rule=this.registeredSimpRule(d.rule,env,d.priority);
            const existing=this.simpRegistry.defaults.get(rule.identity);
            if(existing&&existing.origin===rule.origin)
              throw Error(`Simplification rule ${d.rule.text} is already registered in this module.`);
            if(!existing||rule.priority>existing.priority)this.simpRegistry.defaults.set(rule.identity,rule);
          } else {
            if(this.simpRegistry.sets.get(d.name.text)?.origin===this.moduleName)
              throw Error(`Simplification set ${d.name.text} is already declared in this module.`);
            const rules=d.rules.map(token=>this.registeredSimpRule(token,env,0));
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
      this.rewriteWork=emptyRewriteWork();
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
        const schema=this.schema(expression,env);
        if(schema) {
          schema.binding=this.checker.bindingName?.(d.name.text)??d.name.text;
          schema.levels=[];
          env.set(d.name.text,schema);
          declarations.push({name:d.name.text,status:"not-translated",reason:"Universe schema: each concrete specialization is checked at its use; no single closed translation claimed."});
          declarations.at(-1).rewriteWork={...this.rewriteWork};
          this.onDeclaration?.(d,declarations.at(-1));
          continue;
        }
        const term=this.term(expression,new Map(),env);
        // Normal forms are optional inspection output, not a prerequisite for
        // checking a declaration whose Nat value may have millions of successors.
        const checked=this.normalize?this.checker.verify(term):this.checker.infer(term);
        const native=this.nativeCheck?.(checked.term,checked.type,[],{normalize:false})??checked.native;
        if(native&&!native.ok)throw Error(`Native cubical check rejected: ${native.error}`);
        const definition=this.checker.define?.(d.name.text,checked.term,checked.type)??checked.term;
        this.checker.kernel?.checkDeadline();
        env.set(d.name.text,definition);
        declarations.push({name:d.name.text,status:native?"checked-native-cubical":"checked-cubical-fragment",term:checked.term,type:checked.type,normal:checked.normal,native});
      } catch(error) {
        // Remove a same-named imported symbol: a failed local declaration must
        // never silently refer to that other declaration in subsequent proofs.
        env.set(d.name.text,{tag:"Untranslated",name:d.name.text,binding:this.checker.bindingName?.(d.name.text)??d.name.text,reason:error.message});
        declarations.push({name:d.name.text,status:"not-translated",reason:error.message,
          errorStart:error.offset,errorEnd:error.sourceEnd,blockedBy:error.blockedBy});
      } finally {
        if(previousHints)this.checker.kernel.setUnfoldingHints(previousHints);
      }
      declarations.at(-1).rewriteWork={...this.rewriteWork};
      this.onDeclaration?.(d,declarations.at(-1));
      // Diagnostic observers may reject a late result after cleanup. Such a
      // result must not remain available to subsequent declarations.
      if (declarations.at(-1).status === "not-translated")
        env.set(d.name.text,{tag:"Untranslated",name:d.name.text,binding:this.checker.bindingName?.(d.name.text)??d.name.text,reason:declarations.at(-1).reason});
    }
    return {declarations,env,directives,simpRegistry:this.simpRegistry,
      normalizationVisits:this.checker.steps};
  }
  registeredSimpRule(token,env,priority=0) {
    const observe=this.onReference;
    this.onReference=null;
    let term;
    try {term=this.term({kind:"name",name:token.text,start:token.start,end:token.end},new Map(),env,null);}
    finally {this.onReference=observe;}
    simplificationRule(this.checker,term,new Map());
    return {term,identity:JSON.stringify(term),origin:this.moduleName,priority,
      sourceName:token.text};
  }
  selectedSimpRules(items,ctx,env,only,without=[],witnessNames=[]) {
    const witnesses=witnessNames.map(token=>{
      try {
        const proof=env.get(token.text);
        if(!proof||!this.localSources.has(proof))
          throw Error(`Simplification premise witness must be local: ${token.text}.`);
        this.checker.infer(proof,ctx);
        return proof;
      } catch(error) {throw this.locateProofError(error,token);}
    });
    const selected=only?[]:orderedDefaultRules(this.simpRegistry);
    for(const item of items) {
      const set=item.value.kind==="name"&&!item.reverse
        ? resolveSimpSet(this.simpRegistry,item.value.name):null;
      if(set)selected.push(...set.map(rule=>({...rule,
        sourceStart:item.start,sourceEnd:item.end})));
      else {
        let term;
        try {term=this.term(item.value,ctx,env,null);}
        catch(error) {throw this.locateProofError(error,item);}
        selected.push({term,identity:JSON.stringify(term),reverse:item.reverse,
          sourceText:this.source.slice(item.value.start,item.value.end),
          sourceStart:item.start,sourceEnd:item.end});
      }
    }
    const excluded=new Set();
    for(const token of without) {
      const set=resolveSimpSet(this.simpRegistry,token.text);
      if(set)for(const rule of set)excluded.add(rule.identity);
      else {
        try {
          const term=this.term({kind:"name",name:token.text,start:token.start,end:token.end},ctx,env,null);
          simplificationRule(this.checker,term,ctx);
          excluded.add(JSON.stringify(term));
        } catch(error) {throw this.locateProofError(error,token);}
      }
    }
    let rules;
    const activePremises=[];
    let premiseAttempts=0;
    const solvePremise=(premise,owner,deadline)=>{
      if(activePremises.includes(owner)||activePremises.length>=2)return null;
      if(++premiseAttempts>64)throw Error("Simplification premise-search budget exceeded.");
      this.rewriteWork.premiseAttempts++;
      activePremises.push(owner);
      try {
        const available=rules.filter(rule=>!activePremises.includes(rule.identity));
        const simplified=this.simplifyEqualityGoal(premise,available,ctx,deadline);
        this.rewriteWork.premiseRewriteSteps+=simplified.rewrites;
        const residual=this.checker.nf(simplified.current);
        if(residual.tag!=="Path"||freeDimensions(residual.family).has(residual.dim)
          ||!this.checker.equal(residual.left,residual.right,ctx))return null;
        const base=this.checker.check(T.line(this.fresh("i"),residual.family,residual.left),
          simplified.current,ctx);
        const witness=this.checker.check(simplified.rebuild(base),premise,ctx);
        this.rewriteWork.premiseProofs++;
        const used=simplified.trace.flatMap(step=>[step.rule,...step.premiseRules]);
        return {term:witness,rules:used};
      } finally {activePremises.pop();}
    };
    rules=uniqueSimpRules(selected.filter(rule=>!excluded.has(rule.identity)))
      .map(rule=>{
        let compiled;
        try {compiled=simplificationRule(this.checker,rule.term,ctx,rule.reverse,witnesses,
          (premise,deadline)=>solvePremise(premise,rule.identity,deadline));}
        catch(error) {throw this.locateProofError(error,
          {start:rule.sourceStart,end:rule.sourceEnd});}
        const available=rule.sourceName&&env.get(rule.sourceName);
        const sourceText=rule.sourceText??(available&&JSON.stringify(available)===rule.identity
          ? rule.sourceName:null);
        return {...compiled,identity:rule.identity,reverse:!!rule.reverse,
          sourceStart:rule.sourceStart,sourceEnd:rule.sourceEnd,
          sourceText,displayName:sourceText??(rule.origin&&rule.sourceName
            ? `${rule.origin}.${rule.sourceName}`:"a checked rule")};
      });
    // Premise search closes over this rule list. Freeze validation must replace
    // that list as well as the rules used by the outer simplifier traversal.
    Object.defineProperty(rules,"withSubset",{value:(subset,run)=>{
      const previous=rules;
      rules=subset;
      try {return run();}
      finally {rules=previous;}
    }});
    return rules;
  }
  freezeSimplification(first,rules,trace,replay) {
    if(first.only)return null;
    const used=new Set(trace.flatMap(step=>[step.rule,...step.premiseRules])
      .map(rule=>`${rule.identity}:${rule.reverse}`));
    const frozen=rules.filter(rule=>used.has(`${rule.identity}:${rule.reverse}`));
    if(frozen.some(rule=>!rule.sourceText))return null;
    if(frozen.length<rules.length) {
      const work=this.rewriteWork;
      this.rewriteWork=emptyRewriteWork();
      let valid=false;
      // An omitted rule can change a failed premise search and hence a later
      // rewrite choice. For a simplified hypothesis, replay must also preserve
      // its proof term: later statements may depend on that particular path.
      try {valid=rules.withSubset(frozen,()=>replay?.(frozen)===true);}
      catch {valid=false;}
      finally {this.rewriteWork=work;}
      if(!valid)return null;
    }
    const keyword=first.kind==="simpaOnly"?"simpa":"simp";
    let text=`${keyword} only [${frozen.map(rule=>`${rule.reverse?"<- ":""}${rule.sourceText}`).join(", ")}]`;
    if(first.witnesses?.length)text+=` with [${first.witnesses.map(token=>token.text).join(", ")}]`;
    if(first.at)text+=` at ${first.at.text} as ${first.as.text}`;
    if(first.using)text+=` using ${this.source.slice(first.using.start,first.using.end)}`;
    text+=";";
    return {start:first.start,end:first.end,
      original:this.source.slice(first.start,first.end),text};
  }
  referenceSimplificationSteps(first,trace,ctx,env) {
    for(const [index,step] of trace.entries()) {
      const rule=step.rule.displayName;
      this.onReference?.({name:`simp step ${index+1}`,start:first.start,
        end:first.start+(first.kind==="simpaOnly"?5:4),
        role:"simplification step",expansionIndex:index+1,
        traceParent:first.start,
        description:`${step.phase??"goal"} ${step.side}: checked rewrite ${index+1} using ${step.rule.reverse?"<- ":""}${rule}; ${step.visits} nodes visited.${step.premiseRules.length
          ? ` Premise simplified using ${[...new Set(step.premiseRules.map(item=>item.displayName))].join(", ")}.`:""}`},
        step.witness,new Map(ctx),env);
    }
  }
  term(n,ctx,env,expected=null) {
    const result=this.termBody(n,ctx,env,expected);
    if(this.onReference) {
      let site;
      if(n.kind==="call" && n.fn.kind==="name" && !env.has(n.fn.name)) site=n.fn;
      else if(n.kind==="name" && !env.has(n.name)) site=n;
      else if(n.kind==="binary" && ["=","->","and","or"].includes(n.operator))
        site={name:n.operator,start:n.operatorStart,end:n.operatorEnd};
      else if(["lambda","forall","exists"].includes(n.kind)) {
        const name=n.kind==="lambda"?"fun":n.kind;
        if(this.source.slice(n.start,n.start+name.length)===name)
          site={name,start:n.start,end:n.start+name.length};
      }
      if(Number.isInteger(site?.start)) this.onReference({...site,expressionSite:true,
        role:"language expression",description:`Checked expression: ${this.source.slice(n.start,n.end).trim()}`},
        result,new Map(ctx),env);
    }
    return result;
  }
  termBody(n,ctx,env,expected=null) {
    this.checker.kernel?.checkDeadline();
    if(!n) throw Error("Missing source expression.");
    const tr=(x,e=expected)=>this.term(x,ctx,env,e);
    const inferred=t=>this.checker.infer(t,ctx,new Set(this.dimensions.keys()));
    switch(n.kind) {
      case "withUnfolding": {
        if (!this.checker.scopedUnfolding) throw Error("Unfolding blocks require the native cubical backend.");
        const names=n.hints.map(hint=>{
          let value=env.get(hint.text);
          while(value?.tag==="App")value=value.fn;
          if(value?.tag!=="DefRef")throw Error(`No checked definition to unfold: ${hint.text}`);
          this.onReference?.({...hint,name:hint.text},value,new Map(ctx));
          return value.name;
        });
        return this.checker.scopedUnfolding(names,()=>tr(n.body),ctx,expected);
      }
      case "pathApply": {
        const path=tr(n.left,null);
        return T.at(path,this.interval(n.right,env));
      }
      case "pathLambda": {
        if(!expected)throw Error("path i => ... needs an expected Path or PathP type.");
        const goal=this.checker.nf(expected);
        if(goal.tag!=="Path")throw Error("path i => ... needs an expected Path or PathP type.");
        const dim=this.fresh(n.dimension.text),previous=this.dimensions,checkerDimensions=this.checker.dimensions;
        let index=0;while([...previous.values()].includes(index))index++;
        if(index>=64)throw Error("At most 64 simultaneous cubical dimensions are supported.");
        this.dimensions=new Map(previous).set(dim,index);this.checker.dimensions=this.dimensions;
        try {
          const family=substituteDimension(goal.family,goal.dim,I.variable(dim));
          const scope=new Map(env).set(n.dimension.text,{tag:"Dimension",name:dim});
          const body=this.term(n.body,ctx,scope,family);
          return T.line(dim,family,body);
        } finally {this.dimensions=previous;this.checker.dimensions=checkerDimensions;}
      }
      case "along": {
        const family=tr(n.family,null),path=tr(n.path,null),value=tr(n.value,null);
        const type=this.checker.nf(inferred(path).type);
        if(type.tag!=="Path"||freeDimensions(type.family).has(type.dim))
          throw Error("along requires a homogeneous base path.");
        const dim=this.fresh("i");
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
          this.onReference?.(n,value,new Map(ctx),env);
          return value;
        }
        if(/^U[0-9]+$/.test(n.name))return T.universe(Number(n.name.slice(1)));
        if(n.name==="succ") { const name=this.fresh();return T.lam(name,T.nat,T.succ(T.variable(name))); }
        const builtin={Nat:T.nat,Unit:T.unit,tt:T.point,Void:T.void};
        if(builtin[n.name])return builtin[n.name];
        throw Error(`Untranslated name: ${n.name}`);
      }
      case "number": {let t=T.zero;for(let i=0;i<n.value;i++)t=T.succ(t);
        this.onReference?.({...n,name:String(n.value)},t,new Map(ctx),env);return t;}
      case "binaryNumber": {
        const term=tr(binaryLiteralSyntax(n));
        this.onReference?.({...n,name:`0b${n.digits}`},term,new Map(ctx),env);return term;
      }
      case "binderGroup": {
        const domain=tr(n.domain,null),kind=n.binderKind;
        let inner=new Map(ctx),scope=new Map(env),bodyExpected=expected;
        const names=[];
        for(const token of n.names) {
          const name=this.fresh(token.text),variable=T.variable(name);
          if(kind==="lambda"&&bodyExpected) {
            const pi=this.checker.nf(bodyExpected);
            if(pi.tag!=="Pi")throw Error("Too many lambda binders for the expected type.");
            this.checker.expect(domain,pi.domain,inner);
            bodyExpected=T.app(T.lam(pi.name,pi.domain,pi.body),variable);
          }
          inner=new Map(inner).set(name,domain);scope=new Map(scope).set(token.text,variable);
          this.sourceBinding(token,variable,inner,scope);
          names.push(name);
        }
        let body=this.term(n.body,inner,scope,kind==="lambda"?bodyExpected:null);
        const constructor=kind==="lambda"?T.lam:kind==="forall"?T.pi:T.sigma;
        for(const name of names.reverse())body=constructor(name,domain,body);
        return body;
      }
      case "lambda": case "forall": case "exists": {
        let domain=n.domain?tr(n.domain,null):null;
        if(n.kind==="lambda"&&!domain) {
          if(!expected)throw Error("Untyped lambda requires an expected function type.");
          const pi=this.checker.nf(expected);
          if(pi.tag!=="Pi")throw Error("Untyped lambda requires an expected function type.");
          domain=pi.domain;
        }
        const name=this.fresh(n.name.text),inner=new Map(ctx).set(name,domain),scope=new Map(env).set(n.name.text,T.variable(name));
        this.sourceBinding(n.name,scope.get(n.name.text),inner,scope);
        let bodyExpected=null;
        if(n.kind==="lambda"&&expected) {
          const pi=this.checker.nf(expected);
          if(pi.tag==="Pi")bodyExpected=T.app(T.lam(pi.name,pi.domain,pi.body),T.variable(name));
        }
        const body=this.term(n.body,inner,scope,bodyExpected);
        return (n.kind==="lambda"?T.lam:n.kind==="forall"?T.pi:T.sigma)(name,domain,body);
      }
      case "binary": {
        const left=tr(n.left,null);
        if(["->","and"].includes(n.operator)) return (n.operator==="->"?T.pi:T.sigma)(this.fresh(),left,tr(n.right,null));
        if(n.operator==="or")return T.sum(left,tr(n.right,null));
        if(["+","*","<=","<"].includes(n.operator)) {
          const name=n.operator==="+"?"add":n.operator==="*"?"mul":n.operator==="<"&&env.has("isLt")?"isLt":"le";
          const first=n.operator==="<"&&name==="le"?{kind:"call",fn:{kind:"name",name:"succ"},args:[n.left]}:n.left;
          return tr({kind:"call",fn:{kind:"name",name},args:[first,n.right]},null);
        }
        if(n.operator==="=") {
          const type=n.carrier?tr(n.carrier,null):inferred(left).type;
          return T.path(this.fresh("i"),type,left,tr(n.right,type));
        }
        throw Error(`Untranslated operator: ${n.operator}`);
      }
      case "pair": {
        if(!expected)throw Error("Pair requires an expected type.");
        const sigma=this.checker.nf(expected);if(sigma.tag!=="Sigma")throw Error("Expected a Sigma type for pair.");
        const first=tr(n.left,sigma.domain), family=T.lam(sigma.name,sigma.domain,sigma.body);
        const result=T.pair(expected,first,tr(n.right,T.app(family,first)));
        if(this.onReference && Number.isInteger(n.tupleStart) && n.right.syntheticTuplePair) {
          const expand=node=>node.kind==="pair" ? `(${expand(node.left)}, ${expand(node.right)})`
            : this.source.slice(node.start,node.end).trim();
          const expansion=expand(n);
          for(const [name,start] of [["(",n.tupleStart],[")",n.tupleEnd]])
            this.onReference({...n,name,start,end:start+1,role:"tuple macro",expansion,
              description:`Expands to ${expansion}.`},result,new Map(ctx),env);
        }
        return result;
      }
      case "call": {
        const builtin=n.fn.kind==="name"&&!env.has(n.fn.name)?n.fn.name:null;
        if(["ua","UnivalenceBeta"].includes(builtin)&&n.args.length>=3) {
          const [universe,A,B]=n.args.slice(0,3).map(a=>tr(a,null));
          if(universe.tag!=="U")throw Error("Univalence requires a concrete universe.");
          this.checker.check(A,universe,ctx,new Set(this.dimensions.keys()));
          this.checker.check(B,universe,ctx,new Set(this.dimensions.keys()));
          const build=(A,B)=>{
            const E=halfAdjointEquiv(A,B),en=this.fresh("equivalence"),x=this.fresh("argument");
            return builtin==="ua"?T.lam(en,E,publicUnivalencePath(A,B,T.variable(en),universe.level)):
              T.lam(en,E,T.lam(x,A,publicUnivalenceBeta(A,B,T.variable(en),T.variable(x))));
          };
          let fn;
          if(this.checker.specializeSchema && this.checker.kernel?.optimizations?.reuseChecks !== false) {
            // The computational derivation is generic in A and B. Check that
            // closed function once per universe, then check ordinary applications.
            const generic=this.checker.specializeSchema(`builtin__${builtin}`,[universe.level],()=>{
              const a=this.fresh("sourceType"),b=this.fresh("targetType");
              return T.lam(a,universe,T.lam(b,universe,build(T.variable(a),T.variable(b))));
            });
            fn=T.app(T.app(generic,A),B);
          } else fn=build(A,B);
          for(const arg of n.args.slice(3)) {
            const type=this.checker.nf(inferred(fn).type);
            if(type.tag!=="Pi")throw Error(`Too many arguments to ${builtin}.`);
            fn=T.app(fn,tr(arg,type.domain));
          }
          return fn;
        }
        if(["Truncate","TruncateIntro","TruncateProp","TruncateElim","LEM","Choice"].includes(builtin)) {
          if(!n.args.length)throw Error(`${builtin} needs a universe argument.`);
          const universe=tr(n.args[0],null);
          if(universe.tag!=="U"||!this.checker.assume)throw Error("Logical assumptions require a concrete universe and an explicit native context.");
          let fn=libraryAssumption(this.checker,builtin,universe.level,ctx);
          for(const arg of n.args.slice(1)) {
            const type=this.checker.nf(inferred(fn).type);
            if(type.tag!=="Pi")throw Error(`Too many arguments to ${builtin}.`);
            fn=T.app(fn,tr(arg,type.domain));
          }
          return fn;
        }
        if(builtin==="typed"&&n.args.length===2) {
          const type=tr(n.args[0],null),term=tr(n.args[1],type);
          const checked=this.checker.check(term,type,ctx,new Set(this.dimensions.keys()));
          return this.checker.ascribe?.(checked,type)??checked;
        }
        if(["path","PathP","comp","fill"].includes(builtin)) {
          const size=n.args.length;
          if((builtin==="path"&&size!==2)||(builtin==="PathP"&&size!==3)||(builtin==="comp"&&size<2)||(builtin==="fill"&&size<3))
            throw Error(`Invalid arguments to ${builtin}.`);
          const dim=this.fresh("i"),family=this.dimensionBody(n.args[0],dim,ctx,env);
          if(builtin==="path")return T.line(dim,family,this.dimensionBody(n.args[1],dim,ctx,env,family));
          if(builtin==="PathP")return T.path(dim,family,tr(n.args[1],null),tr(n.args[2],null));
          const system=n.args.slice(builtin==="fill"?3:2).map(part=>{
            if(part.kind==="call"&&part.fn.kind==="name"&&part.fn.name==="face_when"&&part.args.length===2)
              return {face:this.cofibration(part.args[0],env),term:this.dimensionBody(part.args[1],dim,ctx,env,family)};
            if(part.kind!=="call"||part.fn.kind!=="name"||part.fn.name!=="face"||part.args.length!==3)
              throw Error("A composition wall has syntax face(i, 0 or 1, fun (j : Interval) => ...).");
            const [coordinate,endpoint,wall]=part.args;
            if(coordinate.kind!=="name"||env.get(coordinate.name)?.tag!=="Dimension"||endpoint.kind!=="number"||![0,1].includes(endpoint.value))
              throw Error("A composition face needs an outer interval coordinate and endpoint 0 or 1.");
            return {face:F.endpoint(env.get(coordinate.name).name,endpoint.value),term:this.dimensionBody(wall,dim,ctx,env,family)};
          });
          const base=tr(n.args[1],null);
          return builtin==="fill"?withNativeReferences([family,system,base],(family,system,base)=>fill(dim,family,system,base,this.interval(n.args[2],env))):T.comp(dim,family,system,base);
        }
        if(["path_from_transport","path_to_transport"].includes(builtin)&&n.args.length===4) {
          const dim=this.fresh("i"),family=this.dimensionBody(n.args[0],dim,ctx,env);
          const left=tr(n.args[1],null),right=tr(n.args[2],null),value=tr(n.args[3],null);
          return T.app((builtin==="path_from_transport"?transportToDependentPath:dependentPathToTransport)(dim,family,left,right),value);
        }
        if(builtin==="at"&&n.args.length===2)return T.at(tr(n.args[0],null),this.interval(n.args[1],env));
        if(builtin==="pushout_induction"&&n.args.length===5) {
          const [motive,left,right,bridge,value]=n.args.map(a=>tr(a,null));
          return T.app(T.pushElim(motive,left,right,bridge),value);
        }
        if(builtin==="Pushout"&&n.args.length===5) return pushout(...n.args.map(a=>tr(a,null)));
        if(["push_left","push_right"].includes(builtin)&&n.args.length===2)
          return (builtin==="push_left"?T.pushLeft:T.pushRight)(...n.args.map(a=>tr(a,null)));
        if(builtin==="push_path"&&n.args.length===2) {
          const [P,a]=n.args.map(a=>tr(a,null)),i=this.fresh("push");
          return T.line(i,P,T.pushPath(P,a,I.variable(i)));
        }
        if(builtin==="pair_induction"&&n.args.length===3) {
          const [motive,branch,value]=n.args.map(a=>tr(a,null));
          const sigma=this.checker.nf(inferred(value).type);
          if(sigma.tag!=="Sigma")throw Error("pair_induction requires a dependent pair.");
          const x=this.fresh(),y=this.fresh(),first=T.variable(x),second=T.variable(y);
          const fiber=T.app(T.lam(sigma.name,sigma.domain,sigma.body),first);
          const branchType=T.pi(x,sigma.domain,T.pi(y,fiber,
            T.app(motive,T.pair(sigma,first,second))));
          this.checker.check(branch,branchType,ctx,new Set(this.dimensions.keys()));
          // Cubical Sigma eta identifies (fst p, snd p) with p. The native
          // checker verifies the dependent result conversion at the motive.
          const result=T.app(T.app(branch,T.first(value)),T.second(value));
          const type=T.app(motive,value),checked=this.checker.check(result,type,ctx,new Set(this.dimensions.keys()));
          return this.checker.ascribe?.(checked,type)??checked;
        }
        if(builtin==="succ"&&n.args.length===1)return T.succ(tr(n.args[0],T.nat));
        if(builtin==="W"&&n.args.length===2) {
          const domain=tr(n.args[0],null),family=tr(n.args[1],null),name=this.fresh();
          return T.w(name,domain,T.app(family,T.variable(name)));
        }
        if(builtin==="sup"&&n.args.length===3) {
          const type=tr(n.args[0],null),shape=this.checker.nf(type);
          if(shape.tag!=="W")throw Error("sup requires a W type.");
          const label=tr(n.args[1],shape.domain),arity=T.app(T.lam(shape.name,shape.domain,shape.body),label);
          return T.sup(type,label,tr(n.args[2],T.pi(this.fresh(),arity,type)));
        }
        if(builtin==="wrec"&&n.args.length===4) {
          const [type,motive,step,value]=n.args.map(a=>tr(a,null));
          this.checker.check(value,type,ctx,new Set(this.dimensions.keys()));
          return T.wrec(motive,step,value);
        }
        if(builtin==="unit_induction"&&n.args.length===3) {
          const [motive,point,value]=n.args.map(a=>tr(a,null));
          return T.unitrec(motive,point,value);
        }
        if(builtin==="FunExt"&&n.args.length===6) {
          const [universe,A,B,f,g,h]=n.args.map(a=>tr(a,null));
          if(universe.tag!=="U")throw Error("FunExt needs a concrete universe.");
          this.checker.check(A,universe,ctx,new Set(this.dimensions.keys()));
          const x=this.fresh(),dim=this.fresh("i"),variable=T.variable(x),fiber=T.app(B,variable);
          this.checker.check(B,T.pi(x,A,universe),ctx,new Set(this.dimensions.keys()));
          const functionType=T.pi(x,A,fiber);
          this.checker.check(f,functionType,ctx,new Set(this.dimensions.keys()));
          this.checker.check(g,functionType,ctx,new Set(this.dimensions.keys()));
          const pointwise=T.pi(x,A,T.path(dim,fiber,T.app(f,variable),T.app(g,variable)));
          this.checker.check(h,pointwise,ctx,new Set(this.dimensions.keys()));
          return T.line(dim,functionType,T.lam(x,A,T.at(T.app(h,variable),I.variable(dim))));
        }
        if(builtin==="absurd"&&n.args.length===1) {
          if(!expected)throw Error("absurd requires an expected type.");
          return T.abort(expected,tr(n.args[0],T.void));
        }
        if(["left","right"].includes(builtin)&&n.args.length===1) {
          if(!expected)throw Error("Sum injection requires an expected type.");
          const sum=this.checker.nf(expected);
          if(sum.tag!=="Sum")throw Error("Expected a sum type.");
          return (builtin==="left"?T.inl:T.inr)(expected,tr(n.args[0],sum[builtin]));
        }
        if(builtin==="refl"&&n.args.length===1) {
          const value=tr(n.args[0],null);return T.line(this.fresh("i"),inferred(value).type,value);
        }
        if(builtin==="sym"&&n.args.length===1) {
          const p=tr(n.args[0],null),type=this.checker.nf(inferred(p).type);
          if(type.tag!=="Path")throw Error("sym requires a path.");
          // Cubist equality has a constant carrier (dependent Path reversal
          // is checked by the core directly, rather than silently approximated).
          const i=this.fresh("i"),result=T.line(i,type.family,T.at(p,I.reverse(I.variable(i))));
          return this.checker.ascribe && this.checker.kernel?.optimizations?.compactPaths !== false ? this.checker.ascribe(result,T.path(i,type.family,type.right,type.left)) : result;
        }
        if(builtin==="trans"&&n.args.length===2) {
          const p=tr(n.args[0],null),q=tr(n.args[1],null),pt=this.checker.nf(inferred(p).type),qt=this.checker.nf(inferred(q).type);
          if(pt.tag!=="Path"||qt.tag!=="Path")throw Error("trans requires paths.");
          this.checker.expect(pt.family,qt.family,ctx);
          if(!this.checker.equal(pt.right,qt.left,ctx))throw Error("Path endpoints do not match.");
          const i=this.fresh("i"),j=this.fresh("j");
          const result=T.line(j,pt.family,T.comp(i,pt.family,[
            {face:F.endpoint(j,0),term:pt.left},{face:F.endpoint(j,1),term:T.at(q,I.variable(i))},
          ],T.at(p,I.variable(j))));
          // Retain the mathematical endpoints in the inferred signature.
          // The native checker still verifies the composition and conversion.
          return this.checker.ascribe && this.checker.kernel?.optimizations?.compactPaths !== false ? this.checker.ascribe(result,T.path(j,pt.family,pt.left,qt.right)) : result;
        }
        if(builtin==="cong"&&n.args.length===2) {
          const fn=tr(n.args[0],null),p=tr(n.args[1],null),pt=this.checker.nf(inferred(p).type);
          if(pt.tag!=="Path")throw Error("cong requires a path.");
          const left=T.app(fn,pt.left),type=inferred(left).type,i=this.fresh("i");
          const result=T.line(i,type,T.app(fn,T.at(p,I.variable(i))));
          return this.checker.ascribe && this.checker.kernel?.optimizations?.compactPaths !== false ? this.checker.ascribe(result,T.path(i,type,left,T.app(fn,pt.right))) : result;
        }
        if(builtin==="apd"&&n.args.length===4) {
          const [fn,x,y,p]=n.args.map(a=>tr(a,null));
          const pt=this.checker.nf(inferred(p).type),ft=this.checker.nf(inferred(fn).type);
          if(pt.tag!=="Path"||ft.tag!=="Pi"||!this.checker.equal(pt.left,x,ctx)||!this.checker.equal(pt.right,y,ctx))
            throw Error("Dependent action needs a function and a path with the supplied endpoints.");
          const i=this.fresh("i"),family=T.app(T.lam(ft.name,ft.domain,ft.body),T.at(p,I.variable(i)));
          const action=T.line(i,family,T.app(fn,T.at(p,I.variable(i))));
          return T.app(dependentPathToTransport(i,family,T.app(fn,x),T.app(fn,y)),action);
        }
        if(builtin==="apd_path"&&n.args.length===2) {
          const fn=tr(n.args[0],null),p=tr(n.args[1],null);
          const ft=this.checker.nf(inferred(fn).type),pt=this.checker.nf(inferred(p).type);
          if(ft.tag!=="Pi"||pt.tag!=="Path"||freeDimensions(pt.family).has(pt.dim))
            throw Error("apd_path needs a dependent function and a homogeneous path.");
          this.checker.expect(pt.family,ft.domain,ctx);
          const dim=this.fresh("i"),index=T.at(p,I.variable(dim));
          const family=T.app(T.lam(ft.name,ft.domain,ft.body),index);
          return T.line(dim,family,T.app(fn,index));
        }
        if(builtin==="transport"&&n.args.length===5) {
          const [family,x,y,p,value]=n.args.map(a=>tr(a,null));
          const pt=this.checker.nf(inferred(p).type);if(pt.tag!=="Path")throw Error("transport requires a path.");
          if(!this.checker.equal(pt.left,x,ctx)||!this.checker.equal(pt.right,y,ctx))throw Error("Transport endpoints do not match.");
          const i=this.fresh("i");return T.comp(i,T.app(family,T.at(p,I.variable(i))),[],value);
        }
        if(builtin==="path_induction"&&n.args.length===6) {
          const [A,C,d,x,y,p]=n.args.map(a=>tr(a,null)),i=this.fresh("i"),j=this.fresh("j");
          const pt=this.checker.nf(inferred(p).type);
          if(pt.tag!=="Path"||!this.checker.equal(pt.family,A,ctx)||!this.checker.equal(pt.left,x,ctx)||!this.checker.equal(pt.right,y,ctx))throw Error("Path induction endpoints/carrier do not match.");
          const segment=T.line(j,A,T.at(p,I.meet(I.variable(i),I.variable(j))));
          const family=T.app(T.app(T.app(C,x),T.at(p,I.variable(i))),segment);
          return T.comp(i,family,[],T.app(d,x));
        }
        if(builtin==="based_induction"&&n.args.length===8) {
          const [universe,motiveUniverse,A,x,C,d,y,p]=n.args.map(a=>tr(a,null));
          if(universe.tag!=="U"||motiveUniverse.tag!=="U")throw Error("Based induction needs concrete universes.");
          this.checker.check(A,universe,ctx,new Set(this.dimensions.keys()));
          const b=this.fresh(),q=this.fresh(),i=this.fresh("i"),j=this.fresh("j");
          const pathType=T.path(j,A,x,T.variable(b));
          this.checker.check(C,T.pi(b,A,T.pi(q,pathType,motiveUniverse)),ctx,new Set(this.dimensions.keys()));
          this.checker.check(p,T.path(j,A,x,y),ctx,new Set(this.dimensions.keys()));
          const reflexivity=T.line(j,A,x);
          this.checker.check(d,T.app(T.app(C,x),reflexivity),ctx,new Set(this.dimensions.keys()));
          const segment=T.line(j,A,T.at(p,I.meet(I.variable(i),I.variable(j))));
          return T.comp(i,T.app(T.app(C,T.at(p,I.variable(i))),segment),[],d);
        }
        let fn=n.fn.kind==="name"&&env.get(n.fn.name)?.tag==="UniverseSchema"?env.get(n.fn.name):tr(n.fn,null);
        for(const arg of n.args) {
          if(fn.tag==="UniverseSchema") {
            const universe=tr(arg,null);if(universe.tag!=="U")throw Error("Schema requires a concrete universe level.");
            const scope=new Map(fn.env).set(fn.parameter,universe);
            const next=this.schema(fn.body,scope,fn.simpRegistry,fn.moduleName),
              levels=[...(fn.levels??[]),universe.level];
            if(next) { next.binding=fn.binding;next.levels=levels;fn=next; }
            else {
              const schema=fn;
              // The schema body belongs to its definition's source, not this
              // call site. Do not attach its offsets to the caller's file.
              const onReference=this.onReference;
              const previousRegistry=this.simpRegistry,previousModule=this.moduleName;
              this.simpRegistry=copySimpRegistry(schema.simpRegistry);
              this.moduleName=schema.moduleName;
              const sourceNames=new Map();
              this.onReference=(node,term)=>{
                if(node.isBinding&&term.tag==="Var")sourceNames.set(term.name,node.name);
              };
              try {
                fn=this.checker.specializeSchema&&schema.binding
                  ?this.checker.specializeSchema(schema.binding,levels,()=>this.term(schema.body,new Map(),scope,null))
                  :this.term(schema.body,ctx,scope,null);
              } finally {
                this.onReference=onReference;
                this.simpRegistry=previousRegistry;
                this.moduleName=previousModule;
              }
              if(sourceNames.size)this.checker.schemaSourceNames?.set(
                `${schema.binding}__${levels.map(level=>`U${level}`).join("_")}`,sourceNames);
              if(n.fn.kind==="name")this.onReference?.({...n.fn,
                schemaBinding:schema.binding, universes:levels, role:"universe specialization",
                description:`Checked specialization ${n.fn.name}(${levels.map(level=>`U${level}`).join(", ")}) of a library universe template. View source opens the generic definition.`
              },fn,new Map(ctx),env);
            }
            continue;
          }
          const pi=this.checker.nf(inferred(fn).type);if(pi.tag!=="Pi")throw Error("Source application is not a function.");
          fn=T.app(fn,tr(arg,pi.domain));
        }
        if(fn.tag==="UniverseSchema")throw Error("Missing universe arguments.");
        return fn;
      }
      case "induction": {
        const value=tr(n.value,T.nat),k=this.fresh(),ih=this.fresh();
        const stepCtx=new Map(ctx).set(k,T.nat), scope=new Map(env).set(n.index.text,T.variable(k));
        this.sourceBinding(n.index,T.variable(k),stepCtx,scope);
        const motiveBody=this.term(n.type,stepCtx,scope,null),motive=T.lam(k,T.nat,motiveBody);
        const zero=tr(n.base,T.app(motive,T.zero));
        stepCtx.set(ih,motiveBody);scope.set(n.hypothesis.text,T.variable(ih));
        this.sourceBinding(n.hypothesis,T.variable(ih),stepCtx,scope);
        const step=T.lam(k,T.nat,T.lam(ih,motiveBody,this.term(n.step,stepCtx,scope,T.app(motive,T.succ(T.variable(k))))));
        return T.natrec(motive,zero,step,value);
      }
      case "match": {
        const value=tr(n.value,null),type=inferred(value).type,sum=this.checker.nf(type);
        if(sum.tag!=="Sum")throw Error("match requires a sum type.");
        const name=this.fresh(),scope=new Map(env),inner=new Map(ctx).set(name,type);
        if(n.motiveName)scope.set(n.motiveName.text,T.variable(name));
        const motive=T.lam(name,type,this.term(n.type,inner,scope,null));
        const branch=side=>{
          const local=this.fresh(),domain=sum[side],variable=T.variable(local);
          const branchEnv=new Map(env).set(n[side].text,variable);
          const injection=(side==="left"?T.inl:T.inr)(type,variable);
          return T.lam(local,domain,this.term(n[side+"Body"],new Map(ctx).set(local,domain),branchEnv,T.app(motive,injection)));
        };
        return T.sumrec(motive,branch("left"),branch("right"),value);
      }
      case "unpack": {
        const value=tr(n.value,null),sigma=this.checker.nf(inferred(value).type);
        if(sigma.tag!=="Sigma")throw Error("unpack requires a dependent pair.");
        const goal=tr(n.type,null),scope=new Map(env)
          .set(n.left.text,T.first(value)).set(n.right.text,T.second(value));
        const body=this.term(n.body,ctx,scope,goal);
        this.checker.check(body,goal,ctx,new Set(this.dimensions.keys()));
        return body;
      }
      case "proof": {
        const type=tr(n.type,null);
        const term=this.block(n.statements,type,ctx,env);
        const checked=this.checker.check(term,type,ctx,new Set(this.dimensions.keys()));
        return this.checker.ascribe?.(checked,type)??checked;
      }
      default:throw Error(`Untranslated syntax: ${n.kind}`);
    }
  }
  block(statements,goal,ctx,env) {
    try {return this.blockBody(statements,goal,ctx,env);}
    catch(error) {
      throw this.locateProofError(error,statements[0]);
    }
  }
  blockBody(statements,goal,ctx,env) {
    if(!statements.length)throw Error("Proof block has no conclusion.");
    const [first,...rest]=statements;
    if(first.kind==="exact") {
      if(rest.length)throw Error("Statements after exact are unreachable.");
      return this.term(first.value,ctx,env,goal);
    }
    if(first.kind==="rfl") {
      if(rest.length)throw Error("Statements after rfl are unreachable.");
      const path=this.checker.nf(goal);
      if(path.tag!=="Path"||freeDimensions(path.family).has(path.dim))
        throw Error("rfl requires a homogeneous equality goal.");
      const term=T.line(this.fresh("i"),path.family,path.left);
      this.checker.check(term,goal,ctx);
      return term;
    }
    if(first.kind==="calc") {
      if(rest.length)throw Error("Statements after calc are unreachable.");
      const path=this.checker.nf(goal);
      if(path.tag!=="Path"||freeDimensions(path.family).has(path.dim))
        throw Error("calc requires a homogeneous equality goal.");
      if(!first.steps.length)throw Error("calc requires at least one step.");
      let previous=path.left,proof=null;
      for(const [index,step] of first.steps.entries()) {
        const left=step.left.kind==="name"&&step.left.name==="_"?previous:this.term(step.left,ctx,env,path.family);
        if(!this.checker.equal(left,previous,ctx))throw Error("calc step left endpoint does not match the preceding endpoint.");
        const right=this.term(step.right,ctx,env,path.family);
        const target=T.path(this.fresh("i"),path.family,left,right);
        const raw=step.proof.kind==="block"?this.block(step.proof.body,target,ctx,env)
          :this.term(step.proof.value,ctx,env,target);
        const checked=this.checker.check(raw,target,ctx);
        const witness=this.checker.ascribe?.(checked,target)??checked;
        this.onReference?.({...step,name:`calc step ${index+1}`,
          role:"calculation step",expansionIndex:index+1,
          description:`Checked equality step ${index+1} of ${first.steps.length}.`},
          witness,new Map(ctx),env);
        proof=proof?this.composePaths(proof,witness,ctx):witness;
        previous=right;
      }
      if(!this.checker.equal(previous,path.right,ctx))throw Error("calc final endpoint does not match the goal.");
      this.checker.check(proof,goal,ctx);
      this.onReference?.({...first,name:"calc",end:first.start+4,
        role:"calculation witness",description:`Checked ${first.steps.length}-step equality chain.`},
        proof,new Map(ctx),env);
      return proof;
    }
    if(first.kind==="rw") {
      let current=goal;
      let rebuild=proof=>proof;
      const deadline=performance.now()+1000;
      for(const item of first.rules) {
        try {
          const path=this.checker.nf(current);
          if(path.tag!=="Path"||freeDimensions(path.family).has(path.dim))
            throw Error("rw requires a homogeneous equality goal.");
          const rule=equalityRule(this.checker,this.term(item.value,ctx,env,null),ctx,item.reverse);
          let target=first.target,changed;
          if(target) changed=rewriteFirst(this.checker,path[target==="lhs"?"left":"right"],path.family,rule,ctx,first.occurrence,"preorder",deadline,this.rewriteWork);
          else {
            try {changed=rewriteFirst(this.checker,path.left,path.family,rule,ctx,first.occurrence,"preorder",deadline,this.rewriteWork);target="lhs";}
            catch(error) {
              if(error.code!=="REWRITE_OCCURRENCE_MISSING")throw error;
              changed=rewriteFirst(this.checker,path.right,path.family,rule,ctx,
                first.occurrence-error.eligible,"preorder",deadline,this.rewriteWork);target="rhs";
            }
          }
          const next=T.path(this.fresh("i"),path.family,
            target==="lhs"?changed.after:path.left,
            target==="rhs"?changed.after:path.right);
          const previous=rebuild;
          if(target==="lhs")rebuild=proof=>previous(this.composePaths(changed.witness,proof,ctx));
          else {
            const inverse=equalityRule(this.checker,changed.witness,ctx,true).term;
            rebuild=proof=>previous(this.composePaths(proof,inverse,ctx));
          }
          current=next;
        } catch(error) {
          throw this.locateProofError(error,item);
        }
      }
      let proof;
      if(rest.length)proof=this.block(rest,current,ctx,env);
      else {
        const residual=this.checker.nf(current);
        if(!this.checker.equal(residual.left,residual.right,ctx))
          throw Error("rw left an unresolved equality goal; add a following proof statement.");
        proof=T.line(this.fresh("i"),residual.family,residual.left);
        this.checker.check(proof,current,ctx);
      }
      const reconstructed=rebuild(proof);
      this.checker.check(reconstructed,goal,ctx);
      this.onReference?.({...first,name:"rw",end:first.start+2,
        role:"rewrite witness",description:`Checked rewrite using ${first.rules.map(item=>
          this.source.slice(item.value.start,item.value.end)).join(", ")}.`},
        reconstructed,new Map(ctx),env);
      return reconstructed;
    }
    if(first.kind==="simpOnly") {
      const rules=this.selectedSimpRules(first.rules,ctx,env,first.only,first.without,first.witnesses);
      if(first.at) {
        if(!rest.length)throw Error("A simplified hypothesis copy must be followed by a proof statement.");
        const source=env.get(first.at.text);
        if(!source||!this.localSources.has(source))
          throw Error(`simp at requires a local hypothesis: ${first.at.text}.`);
        const originalType=this.checker.infer(source,ctx).type;
        const simplified=this.simplifyEqualityGoal(originalType,rules,ctx);
        const proof=simplified.forward(source);
        const checked=this.checker.check(proof,simplified.current,ctx);
        const named=this.checker.ascribe?.(checked,simplified.current)??checked;
        const scope=new Map(env).set(first.as.text,named);
        this.sourceBinding(first.as,named,ctx,scope);
        const final=this.block(rest,goal,ctx,scope);
        this.onReference?.({...first,name:"simp",end:first.start+4,
          role:"simplification witness",freeze:this.freezeSimplification(first,rules,simplified.trace,
            subset=>{
              const replay=this.simplifyEqualityGoal(originalType,subset,ctx);
              return this.checker.equal(replay.current,simplified.current,ctx)
                &&this.checker.equal(replay.forward(source),named,ctx);
            }),
          description:`Checked simplified hypothesis copy with ${simplified.rewrites} rewrites.`},
          named,new Map(ctx),env);
        this.referenceSimplificationSteps(first,simplified.trace.map(step=>({...step,phase:"hypothesis"})),ctx,env);
        return final;
      }
      if(this.checker.nf(goal).tag!=="Path") {
        const simplified=this.simplifyTypeTerm(goal,rules,ctx);
        if(!rest.length)throw Error("simp left a type goal; add a following proof statement.");
        const proof=this.block(rest,simplified.current,ctx,env);
        const reconstructed=simplified.witness
          ? this.transportTypePath(equalityRule(this.checker,simplified.witness,ctx,true).term,proof,ctx)
          : proof;
        this.checker.check(reconstructed,goal,ctx);
        this.onReference?.({...first,name:"simp",end:first.start+4,
          role:"simplification witness",freeze:this.freezeSimplification(first,rules,simplified.trace,
            subset=>this.checker.equal(
              this.simplifyTypeTerm(goal,subset,ctx).current,simplified.current,ctx)),
          description:`Checked type simplification with ${simplified.rewrites} rewrites.`},
          reconstructed,new Map(ctx),env);
        this.referenceSimplificationSteps(first,simplified.trace.map(step=>({...step,phase:"goal"})),ctx,env);
        return reconstructed;
      }
      const {current,rebuild,rewrites,trace,failures}=this.simplifyEqualityGoal(goal,rules,ctx);
      let proof;
      if(rest.length)proof=this.block(rest,current,ctx,env);
      else {
        const residual=this.checker.nf(current);
        if(!this.checker.equal(residual.left,residual.right,ctx)) {
          const blocked=failures[0];
          const detail=blocked ? ` Rule ${blocked.rule.displayName} has an unproved premise at parameter ${blocked.parameter}; supply a local witness with simp with [name].` : "";
          const error=Error(`simp only left an unresolved equality goal; add a following proof statement.${detail}`);
          throw this.locateProofError(error,blocked?.rule.sourceStart===undefined?first:
            {start:blocked.rule.sourceStart,end:blocked.rule.sourceEnd});
        }
        proof=T.line(this.fresh("i"),residual.family,residual.left);
        this.checker.check(proof,current,ctx);
      }
      const reconstructed=rebuild(proof);
      this.checker.check(reconstructed,goal,ctx);
      this.onReference?.({...first,name:"simp",end:first.start+4,
        role:"simplification witness",freeze:this.freezeSimplification(first,rules,trace,
          subset=>this.checker.equal(
            this.simplifyEqualityGoal(goal,subset,ctx).current,current,ctx)),
        description:`Checked simplification with ${rewrites} rewrites using ${[
          ...new Set(trace.map(step=>step.rule.displayName))].join(", ")||"no theorem rules"}.`},
        reconstructed,new Map(ctx),env);
      this.referenceSimplificationSteps(first,trace,ctx,env);
      return reconstructed;
    }
    if(first.kind==="simpaOnly") {
      if(rest.length)throw Error("Statements after simpa are unreachable.");
      const rules=this.selectedSimpRules(first.rules,ctx,env,first.only,first.without,first.witnesses);
      const value=this.term(first.using,ctx,env,null);
      const suppliedType=this.checker.infer(value,ctx).type;
      const deadline=performance.now()+1000;
      if(this.checker.nf(goal).tag!=="Path") {
        const supplied=this.simplifyTypeTerm(suppliedType,rules,ctx,deadline);
        const target=this.simplifyTypeTerm(goal,rules,ctx,deadline);
        const moved=supplied.witness
          ? this.transportTypePath(supplied.witness,value,ctx):value;
        const checked=this.checker.check(moved,target.current,ctx);
        const result=target.witness
          ? this.transportTypePath(equalityRule(this.checker,target.witness,ctx,true).term,checked,ctx)
          : checked;
        this.checker.check(result,goal,ctx);
        const trace=[...supplied.trace.map(step=>({...step,phase:"supplied"})),
          ...target.trace.map(step=>({...step,phase:"goal"}))];
        this.onReference?.({...first,name:"simpa",end:first.start+5,
          role:"simplification witness",freeze:this.freezeSimplification(first,rules,trace,
            subset=>this.checker.equal(
              this.simplifyTypeTerm(suppliedType,subset,ctx).current,supplied.current,ctx)
              &&this.checker.equal(
                this.simplifyTypeTerm(goal,subset,ctx).current,target.current,ctx)),
          description:`Checked type simpa with ${trace.length} rewrites using ${[
            ...new Set(trace.map(step=>step.rule.displayName))].join(", ")||"no theorem rules"}.`},
          result,new Map(ctx),env);
        this.referenceSimplificationSteps(first,trace,ctx,env);
        return result;
      }
      const supplied=this.simplifyEqualityGoal(suppliedType,rules,ctx,deadline);
      const target=this.simplifyEqualityGoal(goal,rules,ctx,deadline);
      const simplified=supplied.forward(value);
      const checked=this.checker.check(simplified,target.current,ctx);
      const result=target.rebuild(checked);
      this.checker.check(result,goal,ctx);
      const trace=[...supplied.trace.map(step=>({...step,phase:"supplied type"})),
        ...target.trace.map(step=>({...step,phase:"goal"}))];
      this.onReference?.({...first,name:"simpa",end:first.start+5,
        role:"simplification witness",freeze:this.freezeSimplification(first,rules,trace,
          subset=>this.checker.equal(
            this.simplifyEqualityGoal(suppliedType,subset,ctx).current,supplied.current,ctx)
            &&this.checker.equal(
              this.simplifyEqualityGoal(goal,subset,ctx).current,target.current,ctx)),
        description:`Checked simpa with ${trace.length} rewrites using ${[
          ...new Set(trace.map(step=>step.rule.displayName))].join(", ")||"no theorem rules"}.`},
        result,new Map(ctx),env);
      this.referenceSimplificationSteps(first,trace,ctx,env);
      return result;
    }
    if(first.kind==="intro") {
      const pi=this.checker.nf(goal);
      if(pi.tag!=="Pi")throw Error("intro requires a dependent function goal.");
      const name=this.fresh(first.name.text),variable=T.variable(name),inner=new Map(ctx).set(name,pi.domain);
      const scope=new Map(env).set(first.name.text,variable);
      this.sourceBinding(first.name,variable,inner,scope);
      const bodyGoal=T.app(T.lam(pi.name,pi.domain,pi.body),variable);
      return T.lam(name,pi.domain,this.block(rest,bodyGoal,inner,scope));
    }
    if(first.kind==="ext") {
      const path=this.checker.nf(goal);
      if(path.tag!=="Path"||freeDimensions(path.family).has(path.dim))
        throw Error("ext requires equality of functions with a fixed type.");
      const pi=this.checker.nf(path.family);
      if(pi.tag!=="Pi")throw Error("ext requires equality of functions.");
      const name=this.fresh(first.variable.text),variable=T.variable(name);
      const inner=new Map(ctx).set(name,pi.domain),scope=new Map(env).set(first.variable.text,variable);
      this.sourceBinding(first.variable,variable,inner,scope);
      const output=T.app(T.lam(pi.name,pi.domain,pi.body),variable);
      const pointwise=T.path(this.fresh("i"),output,T.app(path.left,variable),T.app(path.right,variable));
      const body=this.block(rest,pointwise,inner,scope);
      const dimension=this.fresh("i");
      return T.line(dimension,path.family,T.lam(name,pi.domain,T.at(body,I.variable(dimension))));
    }
    if(first.kind==="over") {
      if(rest.length)throw Error("Statements after over are unreachable.");
      const target=this.checker.nf(goal);
      if(target.tag!=="Path")throw Error("over requires an expected PathP goal.");
      const C=this.term(first.family,ctx,env,null),p=this.term(first.path,ctx,env,null);
      const base=this.checker.nf(this.checker.infer(p,ctx).type);
      if(base.tag!=="Path"||freeDimensions(base.family).has(base.dim))
        throw Error("over requires a homogeneous base path.");
      const dim=this.fresh("i"),family=T.app(C,T.at(p,I.variable(dim)));
      const transported=T.comp(dim,family,[],target.left);
      const fiber=T.app(C,base.right);
      const obligation=T.path(this.fresh("j"),fiber,transported,target.right);
      const proof=this.block(first.body,obligation,ctx,env);
      const checked=this.checker.check(proof,obligation,ctx);
      const result=T.app(transportToDependentPath(dim,family,target.left,target.right),checked);
      this.checker.check(result,goal,ctx);
      return result;
    }
    if(first.kind==="let"&&first.target.kind==="name") {
      const value=this.term(first.value,ctx,env,null);
      this.checker.infer(value,ctx,new Set(this.dimensions.keys()));
      const scope=new Map(env).set(first.target.name,value);
      this.sourceBinding(first.target,value,ctx,scope);
      return this.block(rest,goal,ctx,scope);
    }
    if(first.kind==="obtain") {
      const value=this.term(first.value,ctx,env,null),scope=new Map(env);
      const bind=(pattern,term)=>{
        if(pattern.kind==="name") {scope.set(pattern.name,term);this.sourceBinding(pattern,term,ctx,scope);return;}
        if(pattern.kind!=="pair"||this.checker.nf(this.checker.infer(term,ctx,new Set(this.dimensions.keys())).type).tag!=="Sigma")
          throw Error("obtain requires a dependent pair matching its pattern.");
        bind(pattern.left,T.first(term));bind(pattern.right,T.second(term));
      };
      this.checker.infer(value,ctx,new Set(this.dimensions.keys()));bind(first.target,value);
      return this.block(rest,goal,ctx,scope);
    }
    if(first.kind==="cases") {
      if(rest.length)throw Error("Statements after cases are not yet translated.");
      const value=this.term(first.value,ctx,env,null),type=this.checker.infer(value,ctx,new Set(this.dimensions.keys())).type;
      const sum=this.checker.nf(type);
      if(sum.tag!=="Sum")throw Error("cases requires a sum type.");
      const motive=T.lam(this.fresh(),type,goal);
      const branch=side=>{
        const name=this.fresh(),domain=sum[side],scope=new Map(env).set(first[side].text,T.variable(name));
        const inner=new Map(ctx).set(name,domain);
        this.sourceBinding(first[side],scope.get(first[side].text),inner,scope);
        return T.lam(name,domain,this.block(first[side+"Body"],goal,inner,scope));
      };
      return T.sumrec(motive,branch("left"),branch("right"),value);
    }
    if(first.kind==="have") {
      const type=this.term(first.type,ctx,env,null),value=this.block(first.body,type,ctx,env);
      const checked=this.checker.check(value,type,ctx,new Set(this.dimensions.keys()));
      // A local lemma keeps its declared signature just like a top-level proof.
      const named=this.checker.ascribe?.(checked,type)??checked;
      const scope=new Map(env).set(first.name.text,named);
      this.sourceBinding(first.name,named,ctx,scope);
      return this.block(rest,goal,ctx,scope);
    }
    if(first.kind==="haveValue") {
      const type=first.type?this.term(first.type,ctx,env,null):null;
      const value=this.term(first.value,ctx,env,type);
      const checked=type?this.checker.check(value,type,ctx):this.checker.infer(value,ctx).term;
      const signature=type??this.checker.infer(checked,ctx).type;
      const named=this.checker.ascribe?.(checked,signature)??checked;
      const scope=new Map(env).set(first.name.text,named);
      this.sourceBinding(first.name,named,ctx,scope);
      return this.block(rest,goal,ctx,scope);
    }
    throw Error(`Proof tactic not yet translated: ${first.kind}`);
  }
  composePaths(left,right,ctx) {
    const p=this.checker.nf(this.checker.infer(left,ctx).type);
    const q=this.checker.nf(this.checker.infer(right,ctx).type);
    if(p.tag!=="Path"||q.tag!=="Path"||freeDimensions(p.family).has(p.dim)||freeDimensions(q.family).has(q.dim))
      throw Error("Expected homogeneous equality paths for composition.");
    this.checker.expect(p.family,q.family,ctx);
    if(!this.checker.equal(p.right,q.left,ctx))throw Error("Path endpoints do not match.");
    const target=T.path(this.fresh("i"),p.family,p.left,q.right);
    const raw=pathConcat(p.family,p.left,left,right);
    const checked=this.checker.check(raw,target,ctx);
    return this.checker.ascribe?.(checked,target)??checked;
  }
  transportTypePath(path,value,ctx) {
    const type=this.checker.nf(this.checker.infer(path,ctx).type);
    if(type.tag!=="Path"||freeDimensions(type.family).has(type.dim)
      ||this.checker.nf(type.family).tag!=="U")
      throw Error("A general goal rewrite requires a checked path of types.");
    this.checker.check(value,type.left,ctx);
    const dim=this.fresh("i");
    const moved=T.comp(dim,T.at(path,I.variable(dim)),[],value);
    return this.checker.check(moved,type.right,ctx);
  }
  simplifyTypeTerm(term,rules,ctx,deadline=performance.now()+1000) {
    const carrier=this.checker.nf(this.checker.infer(term,ctx).type);
    if(carrier.tag!=="U")throw Error("General simplification requires a type-valued goal.");
    let current=term,witness=null,rewrites=0;
    const trace=[],states=new Set();
    while(true) {
      this.checker.kernel?.checkDeadline();
      if(performance.now()>deadline)throw Error("Simplification elapsed-work budget exceeded.");
      const state=JSON.stringify(current);
      if(state.length>250000)throw Error("Simplification term-size budget exceeded.");
      if(states.has(state))throw Error("Simplification cycle detected in the selected rules.");
      states.add(state);
      let selected=null;
      try {
        const result=rewriteFirst(this.checker,current,carrier,rules,ctx,1,
          "postorder",deadline,this.rewriteWork);
        selected={rule:result.rule,result};
      } catch(error) {
        if(error.code!=="REWRITE_OCCURRENCE_MISSING") {
          const rule=error.rewriteRule;
          throw this.locateProofError(error,rule?.sourceStart===undefined?null:
            {start:rule.sourceStart,end:rule.sourceEnd});
        }
      }
      if(!selected)break;
      if(++rewrites>64)throw Error("Simplification rewrite budget exceeded.");
      const {rule,result}=selected;
      witness=witness?this.composePaths(witness,result.witness,ctx):result.witness;
      current=result.after;
      trace.push({side:"type",rule,witness:result.witness,visits:result.visits,
        premiseRules:result.premiseRules});
    }
    return {current,witness,rewrites,trace};
  }
  simplifyEqualityGoal(goal,rules,ctx,deadline=performance.now()+1000) {
    let current=goal,rebuild=proof=>proof,forward=proof=>proof,rewrites=0;
    const trace=[];
    let failures=[];
    const states=new Set();
    while(true) {
      this.checker.kernel?.checkDeadline();
      if(performance.now()>deadline)throw Error("Simplification elapsed-work budget exceeded.");
      const path=this.checker.nf(current);
      if(path.tag!=="Path"||freeDimensions(path.family).has(path.dim))
        throw Error("simp only requires a homogeneous equality goal.");
      const state=JSON.stringify([path.left,path.right]);
      if(state.length>250000)throw Error("Simplification term-size budget exceeded.");
      if(states.has(state))throw Error("Simplification cycle detected in the selected rules.");
      states.add(state);
      for(const rule of rules)rule.clearDiagnostic?.();
      let selected=null;
      for(const side of ["lhs","rhs"]) {
        try {
          const result=rewriteFirst(this.checker,side==="lhs"?path.left:path.right,
            path.family,rules,ctx,1,"postorder",deadline,this.rewriteWork);
          selected={side,result,rule:result.rule};
          break;
        } catch(error) {
          if(error.code!=="REWRITE_OCCURRENCE_MISSING") {
            const rule=error.rewriteRule;
            throw this.locateProofError(error,rule?.sourceStart===undefined?null:
              {start:rule.sourceStart,end:rule.sourceEnd});
          }
        }
      }
      if(!selected) {
        failures=rules.flatMap(rule=>{
          const diagnostic=rule.diagnostic?.();
          return diagnostic?[{rule,...diagnostic}]:[];
        });
        break;
      }
      if(++rewrites>64)throw Error("Simplification rewrite budget exceeded.");
      const {side,result,rule}=selected,previous=rebuild,previousForward=forward;
      trace.push({side,rule,witness:result.witness,visits:result.visits,
        premiseRules:result.premiseRules});
      current=T.path(this.fresh("i"),path.family,
        side==="lhs"?result.after:path.left,
        side==="rhs"?result.after:path.right);
      if(side==="lhs") {
        rebuild=proof=>previous(this.composePaths(result.witness,proof,ctx));
        forward=proof=>this.composePaths(equalityRule(this.checker,result.witness,ctx,true).term,
          previousForward(proof),ctx);
      } else {
        const inverse=equalityRule(this.checker,result.witness,ctx,true).term;
        rebuild=proof=>previous(this.composePaths(proof,inverse,ctx));
        forward=proof=>this.composePaths(previousForward(proof),result.witness,ctx);
      }
    }
    return {current,rebuild,forward,rewrites,trace,failures};
  }
}
