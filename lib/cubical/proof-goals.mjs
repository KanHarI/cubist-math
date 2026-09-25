// Goals, transitions and proof-construction plans (HoTT roadmap A5).
//
// A goal asks for a proof of `target` at an elaboration scope. A tactic makes
// a transition from a goal to the goal that remains, which the statements
// after the tactic prove, and records a plan that rebuilds a proof of the
// remaining goal into a proof of the original. A plan holds only checked
// ingredients, and rebuilding emits ordinary terms that the kernel checks
// again: a plan grants no proof authority.
//
// Plan steps, rebuilt from the last to the first:
// - composition: compose with a checked path `witness` from an endpoint of
//   the goal (`side` "lhs" or "rhs") to that endpoint of the next goal;
// - transport: transport along a checked path of types `witness` from the
//   goal to the next goal;
// - congruence: from pointwise paths under a binder, a path of functions;
// - abstraction: from a proof under a binder, a function;
// - lemma: apply a checked lemma to a proof of its `obligation`.
// Every step rebuilds at the goal's scope. Conversion needs no step: a goal
// whose endpoints agree by conversion is proved by `reflexivity`. Filling
// steps will join these with constructor congruence (A2) and congruence
// lines (A3).
import {T} from "./core.mjs";
import {interval as I} from "./lattice.mjs";
import {freeDimensions} from "./dimension-slots.mjs";
import {pathConcat} from "./path-algebra.mjs";
import {equalityRule} from "./proof-rewrite.mjs";

export class Goal {
  constructor(target,scope) {
    Object.assign(this,{target,scope});
    Object.freeze(this);
  }
  with(target) {return new Goal(target,this.scope);}
  at(scope) {return new Goal(this.target,scope);}
  // The Path head of a homogeneous equality goal, or null.
  equality() {
    const path=this.scope.nf(this.target);
    return path.tag==="Path"&&!freeDimensions(path.family).has(path.dim) ? path : null;
  }
}

// `trace` records the search behind the plan, for inspection.
export class Transition {
  constructor(goal,next=goal,plan=[],trace=[]) {
    Object.assign(this,{goal,next,plan,trace});
    Object.freeze(this);
  }
  extend(step,next,trace=null) {
    return new Transition(this.goal,next,[...this.plan,step],trace?[...this.trace,trace]:this.trace);
  }
  // A proof of the next goal, rebuilt into a proof of the goal.
  rebuild(proof) {
    const {scope}=this.goal;
    for(const step of [...this.plan].reverse()) {
      if(step.kind==="composition")proof=step.side==="lhs"
        ? composePaths(scope,step.witness,proof)
        : composePaths(scope,proof,step.inverse);
      else if(step.kind==="transport")proof=transportTypePath(scope,reverse(scope,step.witness),proof);
      else if(step.kind==="congruence") {
        const dimension=scope.fresh("i");
        proof=T.line(dimension,step.family,T.lam(step.name,step.domain,T.at(proof,I.variable(dimension))));
      }
      else if(step.kind==="abstraction")proof=T.lam(step.name,step.domain,proof);
      else if(step.kind==="lemma")proof=T.app(step.lemma,scope.check(proof,step.obligation));
      else throw Error(`Internal elaboration error: unknown plan step ${step.kind}.`);
    }
    return proof;
  }
  // A proof of the goal carried to a proof of the next goal. Only rewriting
  // steps, which are paths, run forward.
  forward(proof) {
    const {scope}=this.goal;
    for(const step of this.plan) {
      if(step.kind==="composition")proof=step.side==="lhs"
        ? composePaths(scope,reverse(scope,step.witness),proof)
        : composePaths(scope,proof,step.witness);
      else if(step.kind==="transport")proof=transportTypePath(scope,step.witness,proof);
      else throw Error(`Internal elaboration error: a ${step.kind} step has no forward direction.`);
    }
    return proof;
  }
}

const reverse=(scope,path)=>equalityRule(scope,path,true).term;

export const steps = {
  // A right-hand witness is reversed when the step is made; rebuilding uses
  // the reversal.
  composition:(scope,side,witness)=>({kind:"composition",side,witness,
    inverse:side==="rhs"?reverse(scope,witness):null}),
  transport:witness=>({kind:"transport",witness}),
  congruence:(name,domain,family)=>({kind:"congruence",name,domain,family}),
  abstraction:(name,domain)=>({kind:"abstraction",name,domain}),
  lemma:(lemma,obligation)=>({kind:"lemma",lemma,obligation}),
};

// The constant path at the left endpoint of an equality goal, checked by the
// kernel against the goal.
export function reflexivity(goal,path=goal.equality()) {
  const proof=T.line(goal.scope.fresh("i"),path.family,path.left);
  goal.scope.check(proof,goal.target);
  return proof;
}

// That proof when the endpoints agree by conversion, and otherwise null.
export function byConversion(goal) {
  const path=goal.equality();
  return path&&goal.scope.equal(path.left,path.right) ? reflexivity(goal,path) : null;
}

// Compose two checked homogeneous paths. Reconstruction is bounded by the
// number of steps, so only declaration cancellation applies here, never a
// tactic's search time limit.
export function composePaths(scope,left,right) {
  scope.checkDeadline();
  const p=scope.nf(scope.infer(left).type);
  const q=scope.nf(scope.infer(right).type);
  if(p.tag!=="Path"||q.tag!=="Path"||freeDimensions(p.family).has(p.dim)||freeDimensions(q.family).has(q.dim))
    throw Error("Expected homogeneous equality paths for composition.");
  scope.expect(p.family,q.family);
  if(!scope.equal(p.right,q.left))throw Error("Path endpoints do not match.");
  const target=T.path(scope.fresh("i"),p.family,p.left,q.right);
  // Syntax construction stays bounded by its node-visit budget.
  const raw=pathConcat(p.family,p.left,left,right,
    {deadline:Infinity,checkDeadline:()=>scope.checkDeadline()});
  const checked=scope.check(raw,target);
  return scope.ascribe(checked,target);
}

// Transport `value` along a checked path of types.
export function transportTypePath(scope,path,value) {
  const type=scope.nf(scope.infer(path).type);
  if(type.tag!=="Path"||freeDimensions(type.family).has(type.dim)
    ||scope.nf(type.family).tag!=="U")
    throw Error("A general goal rewrite requires a checked path of types.");
  scope.check(value,type.left);
  const dim=scope.fresh("i");
  const moved=T.comp(dim,T.at(path,I.variable(dim)),[],value);
  return scope.check(moved,type.right);
}
