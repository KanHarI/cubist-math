// The explicit context of elaboration, passed down instead of kept in
// translator fields. A source unit is one source being elaborated; a scope is
// a lexical position in it. Both are immutable: binding returns a new scope,
// and a freeze replay elaborates in a derived unit. Neither grants
// authority: every term they help build is checked.
import {NameSupply,stem} from "./names.mjs";
import {freeNames} from "./core.mjs";
import {SearchFuel,DECLARATION_FUEL,emptySearchRecord} from "./fuel.mjs";

export const emptyRewriteWork = () => ({
  traversals:0,candidateVisits:0,eligibleMatches:0,successfulRewrites:0,
  premiseAttempts:0,premiseProofs:0,premiseRewriteSteps:0,
});

// `references` receives inspector records as (node, term, scope, env); null
// collects none. `work` counts one declaration's rewriting search. `fuel`
// (fuel.mjs) is spent by every kernel query at a scope of this unit: a
// declaration's fuel, or a tactic search's, which counts toward it too.
// `searches` records what the declaration's searches spent. `declaring` names
// the declaration being elaborated, for a message about its own name.
export class SourceUnit {
  constructor({checker,source="",moduleName="source",simpRegistry,references=null,
    freezeSuggestions=true,work=emptyRewriteWork(),fuel=null,searches=emptySearchRecord(),
    names=new NameSupply({taken:name=>checker.assumptions?.has(name)}),declaring=null}) {
    Object.assign(this,{checker,source,moduleName,simpRegistry,references,freezeSuggestions,work,fuel,searches,names,declaring});
    Object.freeze(this);
  }
  // A declaration's unit: its own work counters, fuel and record of searches.
  declaration(limits=DECLARATION_FUEL) {
    return this.with({work:emptyRewriteWork(),searches:emptySearchRecord(),
      fuel:new SearchFuel("The declaration's elaboration",limits,{declaration:true})});
  }
  with(changes) {return new SourceUnit({...this,...changes});}
  // Report an error at a source node of this unit, unless it has a position.
  locate(error,node) {
    if(Number.isInteger(error.offset)||!Number.isInteger(node?.start))return error;
    error.offset=node.start;
    error.sourceEnd=node.end;
    const before=this.source.slice(0,error.offset);
    const line=before.split("\n").length;
    const column=error.offset-(before.lastIndexOf("\n")+1)+1;
    error.message+=` at ${line}:${column}`;
    return error;
  }
}

// A lexical scope: the term telescope (`context`, name to type), the source
// names (`env`, source name to term) and the live interval dimensions
// (name to slot). Face restrictions are not represented: the checker's query
// interface has only the unrestricted face. Checker queries at a scope pass
// its context, dimensions and name supply explicitly.
export class Scope {
  constructor(unit,context=new Map(),env=new Map(),dimensions=new Map()) {
    Object.assign(this,{unit,context,env,dimensions});
    Object.freeze(this);
  }
  get checker() {return this.unit.checker;}
  withUnit(unit) {return new Scope(unit,this.context,this.env,this.dimensions);}
  withEnv(env) {return new Scope(this.unit,this.context,env,this.dimensions);}
  alias(name,value) {return this.withEnv(new Map(this.env).set(name,value));}
  // Binding a name that is already in scope would silently rebind it. With
  // unique generated names this is an elaborator bug, never a user error.
  bind(name,type) {
    if(this.context.has(name))throw Error(`Internal elaboration error: ${name} is already bound.`);
    return new Scope(this.unit,new Map(this.context).set(name,type),this.env,this.dimensions);
  }
  bindDimension(name) {
    const dimensions=this.dimensions;
    if(dimensions.has(name))throw Error(`Internal elaboration error: ${name} is already bound.`);
    let index=0;while([...dimensions.values()].includes(index))index++;
    if(index>=64)throw Error("At most 64 simultaneous cubical dimensions are supported.");
    return new Scope(this.unit,this.context,this.env,new Map(dimensions).set(name,index));
  }
  fresh(stem) {return this.unit.names.fresh(stem);}
  checkDeadline() {this.checker.kernel?.checkDeadline();}
  // Each kernel query spends a query of this unit's fuel before it is asked.
  spend(kind,amount=1) {this.unit.fuel?.spend(kind,amount);}
  infer(term) {this.spend("queries");return this.checker.infer(term,this.context,this.dimensions);}
  check(term,type) {this.spend("queries");return this.checker.check(term,type,this.context,this.dimensions);}
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
  // The context a goal display shows, with `terms` shown in it: all of it but
  // a hypothesis that a later one has superseded, as a clause of a match binds
  // a generalized hypothesis again under its source name. No source name
  // reaches the superseded one, its stem now names the later one, and nothing
  // shown mentions it.
  shownContext(terms=[]) {
    const order=new Map([...this.context.keys()].map((name,index)=>[name,index]));
    const reached=new Set([...this.env.values()].filter(value=>value?.tag==="Var").map(value=>value.name));
    const superseded=name=>{
      if(reached.has(name))return false;
      const now=this.env.get(stem(name));
      return now?.tag==="Var"&&order.get(now.name)>order.get(name);
    };
    if(![...order.keys()].some(superseded))return this.context;
    const mentioned=new Set(terms.filter(Boolean).flatMap(term=>[...freeNames(term)]));
    const shown=[];
    for(const [name,type] of [...this.context].reverse()) {
      if(!mentioned.has(name)&&superseded(name))continue;
      shown.unshift([name,type]);
      for(const free of freeNames(type))mentioned.add(free);
    }
    return new Map(shown);
  }
}
