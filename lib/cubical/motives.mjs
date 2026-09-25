// Motive abstraction (HoTT roadmap A5): the motive with which an eliminator
// proves a goal about several scrutinees, independent of any tactic, for
// `match`, registered eliminators and structure descriptions.
//
// Each scrutinee becomes a binder of the motive, in order, so a later
// scrutinee's type can mention an earlier one. A local hypothesis whose type
// mentions a scrutinee, or an earlier such hypothesis, is generalized: the
// motive quantifies over it, each branch introduces it again at the
// constructor, and the eliminator's result is applied to the original.
// Occurrences are found as rewriting matches its rules: variables,
// definitions, numerals and applications, compared syntactically, never under
// a binder of one of the scrutinee's names. The kernel checks the motive and
// every term built from it.
import {T,substituteTerm} from "./core.mjs";
import {syntaxGraphBudget,syntaxNames} from "./syntax-graph.mjs";
import {Goal,Transition,steps} from "./proof-goals.mjs";

const termBinders = new Set(["Pi","Lam","Sigma","W"]);
// The children in which a node binds its dimension.
const dimensionScope = new Map([["Path",["family"]],["PLam",["family","body"]],
  ["Comp",["family","system"]],["HComp",["system"]],["Trans",["family"]]]);

const rigid = (pattern,term) => {
  if(pattern===term)return true;
  if(pattern.tag!==term.tag)return false;
  if(pattern.tag==="Var"||pattern.tag==="DefRef")return pattern.name===term.name;
  if(["Zero","Nat","Unit","Point"].includes(pattern.tag))return true;
  if(pattern.tag==="Succ")return rigid(pattern.value,term.value);
  if(pattern.tag==="App")return rigid(pattern.fn,term.fn)&&rigid(pattern.arg,term.arg);
  return false;
};

// Replace each occurrence of a pattern by its variable. Shared subterms are
// visited once for each set of patterns still active; an unchanged term keeps
// its identity.
function abstractOccurrences(term,patterns,budget) {
  const memo=new WeakMap();
  const visit=(value,active)=>{
    if(!value||typeof value!=="object"||!active.length)return value;
    const key=active.map(pattern=>pattern.index).join(",");
    let cache=memo.get(value);
    if(cache?.has(key))return cache.get(key);
    budget.tick();
    let result=value.tag&&active.find(pattern=>rigid(pattern.term,value))?.variable;
    if(!result) {
      const bound=!value.tag?null:termBinders.has(value.tag)?{name:value.name,keys:["body"]}
        :dimensionScope.has(value.tag)?{name:value.dim,keys:dimensionScope.get(value.tag)}:null;
      let copy=null;
      for(const [field,child] of Object.entries(value)) {
        const inner=bound?.keys.includes(field)?active.filter(pattern=>!pattern.names.has(bound.name)):active;
        const mapped=visit(child,inner);
        if(mapped!==child)(copy??=Array.isArray(value)?[...value]:{...value})[field]=mapped;
      }
      result=copy??value;
    }
    if(!cache)memo.set(value,cache=new Map());
    cache.set(key,result);
    return result;
  };
  return visit(term,patterns);
}

export function abstractMotive(goal,scrutinees) {
  const {scope}=goal;
  const budget=syntaxGraphBudget({deadline:Infinity,checkDeadline:()=>scope.checkDeadline()});
  const patterns=[];
  const pattern=(term,variable)=>patterns.push({term,variable,index:patterns.length,
    names:syntaxNames(term,{deadline:Infinity,checkDeadline:()=>scope.checkDeadline()})});
  const abstract=(term,active=patterns)=>abstractOccurrences(term,active,budget);
  const types=scrutinees.map(scrutinee=>scope.infer(scrutinee).type);
  const binders=scrutinees.map((scrutinee,index)=>{
    const binder={name:scope.fresh(scrutinee.tag==="Var"?scrutinee.name:"scrutinee"),type:abstract(types[index])};
    pattern(scrutinee,T.variable(binder.name));
    return binder;
  });
  const eliminated=new Set(scrutinees.filter(scrutinee=>scrutinee.tag==="Var").map(scrutinee=>scrutinee.name));
  const generalized=[];
  for(const [name,type] of scope.context) {
    if(eliminated.has(name))continue;
    const abstracted=abstract(type);
    if(abstracted===type)continue;
    const hypothesis={name,type:abstracted,binder:scope.fresh(name)};
    generalized.push(hypothesis);
    pattern(T.variable(name),T.variable(hypothesis.binder));
  }
  // The motive binds scrutinees before hypotheses, so no scrutinee may
  // depend on a generalized hypothesis.
  const hypotheses=patterns.slice(scrutinees.length);
  for(const term of [...scrutinees,...types])
    if(abstract(term,hypotheses)!==term)
      throw Error("A scrutinee depends on a hypothesis about another scrutinee; eliminate that hypothesis too.");
  let body=abstract(goal.target);
  for(const hypothesis of [...generalized].reverse())body=T.pi(hypothesis.binder,hypothesis.type,body);
  let term=body;
  for(const binder of [...binders].reverse())term=T.lam(binder.name,binder.type,term);
  scope.infer(term);
  return Object.freeze({term,binders,generalized,
    // The goal of a branch: the motive at the constructor values, at the
    // branch's scope.
    instance(values,at=scope) {
      if(values.length!==binders.length)
        throw Error("Internal elaboration error: a motive instance needs one value per scrutinee.");
      // A motive that does not depend on its scrutinees keeps the goal itself.
      let target=body;
      if(body!==goal.target)
        for(const [index,value] of values.entries())target=substituteTerm(target,binders[index].name,value);
      return new Goal(target,at);
    },
    // Introduce the generalized hypotheses in a branch goal from instance().
    // `renamed` maps each hypothesis to its variable in the branch, so that
    // its source names can be bound again.
    introduce(branch) {
      let {scope:at,target}=branch;
      const plan=[],renamed=new Map();
      for(const hypothesis of generalized) {
        const name=at.fresh(hypothesis.name),variable=T.variable(name);
        at=at.bind(name,target.domain);
        plan.push(steps.abstraction(name,target.domain));
        target=substituteTerm(target.body,target.name,variable);
        renamed.set(hypothesis.name,variable);
      }
      return {transition:new Transition(branch,new Goal(target,at),plan),renamed};
    },
    // The eliminator's result, a proof of the motive at the scrutinees,
    // applied to the generalized hypotheses: a proof of the goal.
    apply(result) {
      return generalized.reduce((term,hypothesis)=>T.app(term,T.variable(hypothesis.name)),result);
    },
  });
}
