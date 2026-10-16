// The explicit context of elaboration, passed down instead of kept in
// translator fields. A source unit is one source being elaborated; a scope is
// a lexical position in it. Both are immutable: binding returns a new scope,
// and a freeze replay elaborates in a derived unit. Neither grants
// authority: every term they help build is checked.
import {propagateElaborationStop} from "./control.mjs";
import {NameSupply} from "./names.mjs";
import {T,freeNames,onFace,substituteTerm,isTerm} from "./core.mjs";
import {SearchFuel,DECLARATION_FUEL,emptySearchRecord} from "./fuel.mjs";
import {ObservationFrame} from "./observations.mjs";
import {BindingAdapter,SlotOutcomes,bindingResolution} from "../cubist/bindings.mjs";
import {substitutionFrame} from "../cubist/source-syntax.mjs";
import {diagnosticCode} from "../diagnostics.mjs";

export const emptyRewriteWork = () => ({
  traversals:0,candidateVisits:0,eligibleMatches:0,successfulRewrites:0,
  premiseAttempts:0,premiseProofs:0,premiseRewriteSteps:0,
});

// `references` receives inspector records as (node, term, scope, env); null
// collects none. `work` counts one declaration's rewriting search. `fuel`
// (fuel.mjs) is spent by every kernel query at a scope of this unit: a
// declaration's fuel, or a tactic search's, which counts toward it too.
// `searches` records what the declaration's searches spent. `declaring` holds
// the declaration's name and kind, for scope labels and self-reference policy.
export class SourceUnit {
  constructor({checker,source="",sources=null,moduleName="source",simpRegistry,references=null,steps=null,observations=null,
    freezeSuggestions=true,work=emptyRewriteWork(),fuel=null,searches=emptySearchRecord(),
    names=new NameSupply({taken:name=>checker.assumptions?.has(name)}),declaring=null,bindingAdapter=null,
    scopePoints=null,contextOwner=null,scopeUnavailable=null,blameSite=null}) {
    observations ??= new ObservationFrame({reference:references,step:steps});
    Object.assign(this,{checker,source,sources,moduleName,simpRegistry,references,steps,observations,freezeSuggestions,work,fuel,searches,names,declaring,bindingAdapter,scopePoints,contextOwner,scopeUnavailable,blameSite});
    Object.freeze(this);
  }
  // A declaration's unit: its own work counters, fuel and record of searches.
  declaration(limits=DECLARATION_FUEL) {
    return this.with({work:emptyRewriteWork(),searches:emptySearchRecord(),observations:this.observations.declaration(),
      contextOwner:this.scopePoints?.owner(this.moduleName)??null,
      fuel:new SearchFuel("The declaration's elaboration",limits,{declaration:true})});
  }
  with(changes) {return new SourceUnit({...this,...changes});}
  recordReference(...record) {this.observations.recordTo("reference",this.references,...record);}
  recordStep(record) {this.observations.recordTo("step",this.steps,record);}
  text(node) {
    const site=substitutionFrame(node)?.site??node;
    const module=site.origin?.module??site.module??this.moduleName;
    const source=module===this.moduleName?this.source:this.sources?.[module];
    return source!==undefined&&Number.isInteger(site.start)&&Number.isInteger(site.end)
      ?source.slice(site.start,site.end):null;
  }
  // Locate once in a source-qualified context. A copied expression reports
  // at its caller and retains the authored span as a related location; no
  // catch may interpret a producer's offsets in the consumer's source.
  locate(error,node) {
    propagateElaborationStop(error);
    if(error.diagnostic)return error;
    const origin=error.origin??node?.origin;
    const span=site=>site&&Number.isInteger(site.start)?{module:site.module??site.origin?.module??this.moduleName,
      start:site.start,end:site.end}:null;
    const copied=origin?.expansion?.findLast(frame=>frame.kind!=="generation"&&frame.site.module===this.moduleName);
    const authored=span(error.origin??(Number.isInteger(error.offset)?{start:error.offset,end:error.sourceEnd}:node));
    const primary=span(this.blameSite??copied?.site)??authored;
    if(!primary)return error;
    const related=[authored,...(origin?.expansion??[]).map(frame=>frame.site)].map(span)
      .filter(site=>site&&(site.module!==primary.module||site.start!==primary.start||site.end!==primary.end));
    error.diagnostic={code:diagnosticCode(error.message),parameters:error.parameters??{},
      kind:error.kind??"elaboration",primary,related:[...new Map(related.map(site=>[JSON.stringify(site),site])).values()]};
    const located=Number.isInteger(error.offset);
    error.offset=primary.module===this.moduleName?primary.start:undefined;
    error.sourceEnd=primary.module===this.moduleName?primary.end:undefined;
    if(located||!Number.isInteger(error.offset))return error;
    const before=this.source.slice(0,error.offset);
    const line=before.split("\n").length;
    const column=error.offset-(before.lastIndexOf("\n")+1)+1;
    error.message+=` at ${line}:${column}`;
    return error;
  }
}

// The environment key of the superseded hypotheses (Scope.supersede): a key
// no source name can spell.
const SUPERSEDED="\u0000superseded";
// A name bound here hides the declarations under that name elsewhere: in
// def f(B : Monoid(U0)), B.one is the field of the parameter B, not a
// declaration B.one, as of a theory or an initial model named B. Hidden,
// each is kept by its name for the translator's own references to it
// (declared).
const HIDDEN="\u0000hidden",identifier=/^[A-Za-z_][A-Za-z0-9_]*$/;
function hide(env,name) {
  if(!identifier.test(name))return;
  const prefix=`${name}.`;
  let hidden=null;
  for(const [key,entry] of env)if(key.startsWith(prefix)) {
    (hidden??=new Map(env.get(HIDDEN))).set(key,entry);
    env.delete(key);
  }
  if(hidden)env.set(HIDDEN,hidden);
}

// A lexical scope: the term telescope (`context`, name to type), the source
// names (`env`, source name to term) and the live interval dimensions
// (name to slot). A face is represented by its restriction: on a face of one
// clause, each type of the context is at the clause's endpoints (onFace).
// Checker queries at a scope pass its context, dimensions and name supply
// explicitly.
export class Scope {
  constructor(unit,context=new Map(),env=new Map(),dimensions=new Map(),slotOutcomes=new SlotOutcomes(),sourceBindings=new Map(),localSources=new Map(),evidence=[],lexical=undefined) {
    if(lexical===undefined) {
      lexical=null;
      if(unit.scopePoints)try {lexical=unit.scopePoints.sourceContext(env);}
      catch(error) {unit=unit.with({scopeUnavailable:error.message});}
    }
    Object.assign(this,{unit,context,env,dimensions,slotOutcomes,sourceBindings,localSources,evidence,lexical});
    Object.freeze(this);
  }
  get checker() {return this.unit.checker;}
  with({unit=this.unit,context=this.context,env=this.env,dimensions=this.dimensions,
    slotOutcomes=this.slotOutcomes,sourceBindings=this.sourceBindings,localSources=this.localSources,evidence=this.evidence,lexical=this.lexical}) {
    return new Scope(unit,context,env,dimensions,slotOutcomes,sourceBindings,localSources,evidence,lexical);
  }
  withUnit(unit) {return this.with({unit});}
  withEnv(env) {return this.with({env});}
  withSlotOutcomes(slotOutcomes) {return this.with({slotOutcomes});}
  // Evidence belongs to the checked model, independently of aliases used
  // to display or open it. A reserved or refused projection grants nothing.
  modelEvidence(model,type=null) {
    if(!isTerm(model))return this;
    if(!this.checker.theories?.size)return this;
    if(this.evidence.some(e=>e.model===model||model.tag==="Var"&&e.model.tag==="Var"&&e.model.name===model.name))return this;
    let head=type??this.infer(model).type;
    const arguments_=[];
    while(head?.tag==="App"||head?.tag==="LApp") {arguments_.unshift(head);head=head.fn;}
    const record=head?.tag==="DefRef"?this.checker.theories.get(head.name):null;
    if(!record)return this;
    const adapter=new BindingAdapter(this.checker.compilationBindings.table),added=[];
    for(const field of record.fields.filter(field=>field.kind==="evidence")) {
      const projection=this.env.get(adapter.key(field.projectionId));
      if(projection?.tag!=="DefRef")continue;
      let term=projection;
      for(const argument of arguments_)term=argument.tag==="LApp"?T.levelApply(term,argument.level):T.app(term,argument.arg);
      const checked=this.infer(T.app(term,model));
      added.push({term:checked.term,type:checked.type,model,dependencies:[record.modelId,field.projectionId]});
    }
    return added.length?this.with({evidence:[...this.evidence,...added]}):this;
  }
  refineEvidence(values) {
    if(!values.size||!this.evidence.length)return this;
    const replace=term=>[...values].reduce((term,[name,value])=>substituteTerm(term,name,value),term);
    return this.with({evidence:this.evidence.map(e=>({...e,term:replace(e.term),type:replace(e.type),model:replace(e.model)}))});
  }
  sourceBinding(name,value,record,source=null) {
    // Retained/query introductions already own an ID without an observer.
    record??=this.unit.bindingAdapter?.bindingForKey(name);
    // Keep an exact value for an outer binding even after its public label
    // is shadowed. These private aliases never introduce source visibility.
    const key=record?new BindingAdapter(this.checker.compilationBindings.table).key(record.id):name;
    const scope=this.aliases(key===name?[[name,value]]:[[name,value],[key,value]]);
    if(!record&&!source)return scope;
    const sourceBindings=new Map(scope.sourceBindings),localSources=new Map(scope.localSources);
    const label=record?.label??source?.name??name;
    // Execution keys may differ even when a source label is shadowed.
    // Keep the old receipt for refinement, but revoke its search visibility.
    for(const [key,entry] of localSources)if(entry.name===label)localSources.delete(key);
    if(record) {
      // Remember the introduction's refinement behavior even after shadowing.
      // Opened-member receipts have no source-local metadata and stay distinct.
      const receipt=Object.freeze({binding:record,local:!!source});
      for(const at of new Set([name,key]))sourceBindings.set(at,receipt);
    }
    // Only the introduced key is a semantic local. An identity receipt must
    // not add evidence or keep a shadowed let visible to proof search.
    if(source)localSources.set(name,Object.freeze({...source,key:name}));
    const lexical=record&&record.label!=="_"&&scope.lexical
      ?scope.lexical.bind(record.label,bindingResolution(record.id)):scope.lexical;
    return scope.with({sourceBindings,localSources,lexical});
  }
  // The scope on a face, Γ, φ: a part of a partial element is translated
  // there, where each of the face's coordinates is its endpoint, in the
  // source as in the types of the context. On a face of more than one
  // clause, the scope as it is.
  onFace(face) {
    if(face.length!==1)return this;
    const ends=new Map(face[0].map(literal=>[literal.slice(0,literal.lastIndexOf(":")),literal.endsWith(":1")?1:0]));
    const env=new Map([...this.env].map(([name,value])=>
      [name,value?.tag==="Dimension"&&ends.has(value.name)?{...value,endpoint:ends.get(value.name)}:value]));
    return this.with({context:new Map([...this.context].map(([name,type])=>[name,onFace(type,face)])),env,
      evidence:this.evidence.map(e=>({...e,term:onFace(e.term,face),type:onFace(e.type,face),model:onFace(e.model,face)}))});
  }
  alias(name,value) {
    return this.aliases([[name,value]]);
  }
  // Refinement changes a value at the same lexical binding. Introduction
  // (alias/sourceBinding) must never inherit a shadowed binder's identity.
  refine(name,value) {
    if(!this.env.has(name))throw new TypeError("Cannot refine an absent binding.");
    const env=new Map(this.env).set(name,value),record=this.sourceBindings.get(name)?.binding;
    if(record)env.set(new BindingAdapter(this.checker.compilationBindings.table).key(record.id),value);
    return this.withEnv(env);
  }
  // Several names at once, with one copy of the names in scope.
  aliases(pairs) {
    pairs=[...pairs];
    if(!pairs.length)return this;
    const env=new Map(this.env);
    const sourceBindings=new Map(this.sourceBindings),localSources=new Map(this.localSources);
    for(const [name,value] of pairs){hide(env,name);env.set(name,value);sourceBindings.delete(name);localSources.delete(name);}
    // Public aliases (including model openings) also shadow retained locals
    // whose execution keys are private identities.
    const labels=new Set(pairs.map(([name])=>name));
    for(const [key,entry] of localSources)if(labels.has(entry.name))localSources.delete(key);
    return this.with({env,sourceBindings,localSources});
  }
  // The source name bound here that hides the declaration `name`, or null.
  hiding(name) {return this.env.get(HIDDEN)?.has(name)&&!this.env.has(name)?name.slice(0,name.indexOf(".")):null;}
  // A node naming a declaration, m.f, as the translator refers to it: where
  // a binding of m hides it, in a scope where it is visible again. Only the
  // declaration is: a call's arguments are read here, where m.f is m's
  // field, as in rebuild(m.f).f.
  declared(node) {
    const name=node.kind==="call"?node.fn.name:node.name;
    if(!this.hiding(name))return node;
    const here=arg=>({kind:"scoped",node:arg,scope:this,start:arg.start,end:arg.end});
    const callee=node.kind==="call"?{...node,args:node.args.map(here)}:node;
    return {kind:"scoped",node:callee,scope:this.withEnv(new Map(this.env).set(name,this.env.get(HIDDEN).get(name))),start:node.start,end:node.end};
  }
  // Binding a name that is already in scope would silently rebind it. With
  // unique generated names this is an elaborator bug, never a user error.
  bind(name,type) {
    if(this.context.has(name))throw Error(`Internal elaboration error: ${name} is already bound.`);
    return this.with({context:new Map(this.context).set(name,type)}).modelEvidence(T.variable(name),type);
  }
  bindDimension(name) {
    const dimensions=this.dimensions;
    if(dimensions.has(name))throw Error(`Internal elaboration error: ${name} is already bound.`);
    let index=0;while([...dimensions.values()].includes(index))index++;
    if(index>=64)throw Error("At most 64 simultaneous cubical dimensions are supported.");
    return this.with({dimensions:new Map(dimensions).set(name,index)});
  }
  // A name from the unit's supply that nothing here binds: a scope built
  // apart from elaboration may bind names another supply gave.
  fresh(stem) {
    let name;
    do name=this.unit.names.fresh(stem); while(this.context.has(name)||this.dimensions.has(name));
    return name;
  }
  checkDeadline() {this.checker.kernel?.checkDeadline();}
  // Each kernel query spends a query of this unit's fuel before it is asked.
  spend(kind,amount=1) {this.unit.fuel?.spend(kind,amount);}
  infer(term) {this.spend("queries");return this.checker.infer(term,this.context,this.dimensions);}
  check(term,type,site=null) {
    this.spend("queries");
    try {return this.checker.check(term,type,this.context,this.dimensions);}
    catch(error) {throw site?this.unit.locate(error,site):error;}
  }
  // A speculative check: {ok:true,term}, or {ok:false,failure,error} with
  // failure "mismatch", "budget" or "deadline". No caller reads the message.
  attempt(term,type) {this.spend("queries");return this.checker.attempt(term,type,this.context,this.dimensions);}
  // Whether `term` has `type`. Only a mismatch answers no: running out of
  // steps or time ends the search that asked.
  accepts(term,type) {
    const result=this.attempt(term,type);
    if(result.ok||result.failure==="mismatch")return result.ok;
    throw result.error;
  }
  nf(term) {this.spend("queries");return this.checker.nf(term,this.dimensions);}
  // The next clause's type of an eliminator (H1), from the kernel.
  clauseType(motive,clauses) {this.spend("queries");return this.checker.nextClauseType(motive,clauses,this.context,this.dimensions);}
  equal(left,right) {this.spend("queries");return this.checker.equal(left,right,this.context,this.dimensions,this.unit.names);}
  expect(actual,expected) {this.spend("queries");return this.checker.expect(actual,expected,this.context,this.dimensions,this.unit.names);}
  // Keep a declared signature on a checked term; the identity is itself checked.
  ascribe(term,type) {return this.checker.ascribe?.(term,type,this.unit.names)??term;}
  // A scope where each hypothesis of `names` is superseded: a later one has
  // taken its source name, as a clause of a match binds a generalized
  // hypothesis again.
  supersede(names) {return this.alias(SUPERSEDED,new Set([...(this.env.get(SUPERSEDED)??[]),...names]));}
  // The context a goal display shows, with `terms` shown in it: all of it but
  // a superseded hypothesis that nothing shown mentions.
  shownContext(terms=[]) {
    const superseded=this.env.get(SUPERSEDED);
    if(![...this.context.keys()].some(name=>superseded?.has(name)))return this.context;
    const mentioned=new Set(terms.filter(Boolean).flatMap(term=>[...freeNames(term)]));
    const shown=[];
    for(const [name,type] of [...this.context].reverse()) {
      if(superseded.has(name)&&!mentioned.has(name))continue;
      shown.unshift([name,type]);
      for(const free of freeNames(type))mentioned.add(free);
    }
    return new Map(shown);
  }
}
