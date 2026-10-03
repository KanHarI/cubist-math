// Proof-block statements: exact, rfl, calc, rw, simp only, simpa, intro,
// hlevel, ext, over, let, obtain, match and cases. tacticProof elaborates a
// block's first statement into a proof of the goal, with the rest of the
// block after it, or returns undefined when it is no statement here.
import {calcStepSite} from "../cubist/link-sites.mjs";
import {T} from "./core.mjs";
import {interval as I} from "./lattice.mjs";
import {freeDimensions} from "./dimension-slots.mjs";
import {transportToDependentPath} from "./path-over.mjs";
import {Goal,Transition,steps,reflexivity,composePaths} from "./proof-goals.mjs";
import {elaborateMatchStatement} from "./match.mjs";

// A conditional rule whose premises cannot be proved stops firing after this
// many distinct premise searches in one simplification; it does not fail it.
export const PREMISE_ATTEMPT_LIMIT = 64;

export const dependentNote = " Some rule matches were skipped because they occur in a dependent "+
  "position; rewrite there with an explicit cong context.";

export function tacticProof(t,first,rest,goal) {
  return Object.hasOwn(tactics,first.kind) ? tactics[first.kind](t,first,rest,goal) : undefined;
}

const tactics = {
  exact(t,first,rest,goal) {
    const {scope}=goal;
    if(rest.length)throw Error("Statements after exact are unreachable.");
    return t.term(first.value,scope,goal.target);
  },
  rfl(t,first,rest,goal) {
    const {scope}=goal;
    if(rest.length)throw Error("Statements after rfl are unreachable.");
    const path=goal.equality();
    if(!path)throw Error("rfl requires a homogeneous equality goal.");
    return reflexivity(goal,path);
  },
  calc(t,first,rest,goal) {
    const {scope}=goal;
    if(rest.length)throw Error("Statements after calc are unreachable.");
    const path=goal.equality();
    if(!path)throw Error("calc requires a homogeneous equality goal.");
    if(!first.steps.length)throw Error("calc requires at least one step.");
    // calc does no search: each step's proof is ordinary elaboration, and
    // composing the checked steps is bounded by their number.
    let previous=path.left,proof=null;
    for(const [index,step] of first.steps.entries()) {
      scope.checkDeadline();
      const left=step.left.kind==="name"&&step.left.name==="_"?previous:t.term(step.left,scope,path.family);
      if(!scope.equal(left,previous)) {
        const [starts,ends]=t.termTexts([left,previous]);
        throw Error(`calc step left endpoint does not match the preceding endpoint. The step starts at ${
          starts}; the chain so far ends at ${ends}.`);
      }
      const right=t.term(step.right,scope,path.family);
      const target=T.path(scope.fresh("i"),path.family,left,right);
      const raw=step.proof.kind==="block"?t.block(step.proof.body,goal.with(target))
        :t.term(step.proof.value,scope,target);
      const checked=scope.check(raw,target);
      const witness=scope.ascribe(checked,target);
      t.reference(scope,{...calcStepSite(step,index),
        description:`Checked equality step ${index+1} of ${first.steps.length}.`},witness);
      proof=proof?composePaths(scope,proof,witness):witness;
      previous=right;
    }
    if(!scope.equal(previous,path.right)) {
      const [ends,right]=t.termTexts([previous,path.right]);
      throw Error(`calc final endpoint does not match the goal. The chain ends at ${ends}; the goal's right side is ${right}.`);
    }
    scope.check(proof,goal.target);
    t.recordTactic(first,scope,proof,{description:`Checked ${first.steps.length}-step equality chain.`});
    return proof;
  },
  rw(t,first,rest,goal) {
    const {scope}=goal,{unit}=scope;
    let transition=new Transition(goal);
    // Each rule's rewrite, for a diagnostic: the side it changed.
    const rewrites=[];
    for(const item of first.rules) {
      try {transition=t.rewriteGoal(transition,first,item,rewrites);}
      catch(error) {throw unit.locate(t.stopped(error,transition.next,rewrites),item);}
    }
    const proof=t.remaining(rest,transition.next,
      ()=>Error(`rw left an unresolved equality goal; add a following proof statement.${
        t.residual(transition.next,rewrites)}`));
    return t.conclude(first,transition,proof,()=>({
      description:`Checked rewrite using ${first.rules.map(item=>
        unit.source.slice(item.value.start,item.value.end)).join(", ")}.`}));
  },
  simpOnly(t,first,rest,goal) {
    const {scope}=goal,{unit,env}=scope;
    const rules=t.preparedRules(first,scope,goal);
    if(first.at) {
      if(!rest.length)throw Error("A simplified hypothesis copy must be followed by a proof statement.");
      const source=env.get(first.at.text);
      if(!source||!t.localSources.has(source))
        throw Error(`simp at requires a local hypothesis: ${first.at.text}.`);
      // The hypothesis's statement is simplified and its proof carried forward.
      const hypothesis=goal.with(scope.infer(source).type);
      const {transition}=t.simplifyEqualityGoal(hypothesis,rules);
      const simplified=transition.next.target;
      const checked=scope.check(transition.forward(source),simplified);
      const named=scope.ascribe(checked,simplified);
      const final=t.block(rest,goal.at(t.sourceBinding(first.as,named,scope)));
      if(unit.references)t.recordTactic(first,scope,named,{
        freeze:t.freezeSimplification(first,rules,transition.trace,scope,(subset,at)=>{
          const replay=t.simplifyEqualityGoal(hypothesis.at(at),subset).transition;
          return at.equal(replay.next.target,simplified)&&at.equal(replay.forward(source),named);
        }),
        description:`Checked simplified hypothesis copy with ${transition.trace.length} rewrites.`},
        transition.trace.map(step=>({...step,phase:"hypothesis"})));
      return final;
    }
    if(scope.nf(goal.target).tag!=="Path") {
      const {transition}=t.simplifyTypeTerm(goal,rules);
      if(!rest.length)throw Error(`simp left a type goal; add a following proof statement.${
        t.residual(transition.next,transition.trace)}`);
      const proof=t.block(rest,transition.next);
      return t.conclude(first,transition,proof,result=>({
        freeze:t.freezeSimplification(first,rules,transition.trace,scope,(subset,at)=>{
          const replay=t.simplifyTypeTerm(goal.at(at),subset).transition;
          return at.equal(replay.next.target,transition.next.target)&&at.equal(replay.rebuild(proof),result);
        }),
        description:`Checked type simplification with ${transition.trace.length} rewrites.`}),
        transition.trace.map(step=>({...step,phase:"goal"})));
    }
    const {transition,failures,dependent}=t.simplifyEqualityGoal(goal,rules);
    const proof=t.remaining(rest,transition.next,()=>{
      const blocked=failures[0];
      const detail=(blocked ? ` Rule ${blocked.rule.displayName} has an unproved premise at parameter ${blocked.parameter}; supply a local witness with simp with [name].${
        rules.premiseSearchExhausted?` Premise search stopped after ${PREMISE_ATTEMPT_LIMIT} attempts.`:""}` : "")
        +(dependent?dependentNote:"");
      const error=Error(`simp only left an unresolved equality goal; add a following proof statement.${detail}${
        t.residual(transition.next,transition.trace)}`);
      return unit.locate(error,blocked?.rule.sourceStart===undefined?first:
        {start:blocked.rule.sourceStart,end:blocked.rule.sourceEnd});
    });
    return t.conclude(first,transition,proof,result=>({
      freeze:t.freezeSimplification(first,rules,transition.trace,scope,(subset,at)=>{
        const replay=t.simplifyEqualityGoal(goal.at(at),subset).transition;
        return at.equal(replay.next.target,transition.next.target)&&at.equal(replay.rebuild(proof),result);
      }),
      description:`Checked simplification with ${transition.trace.length} rewrites using ${[
        ...new Set(transition.trace.map(step=>step.rule.displayName))].join(", ")||"no theorem rules"}.`}),
      transition.trace);
  },
  simpaOnly(t,first,rest,goal) {
    const {scope}=goal;
    if(rest.length)throw Error("Statements after simpa are unreachable.");
    const rules=t.preparedRules(first,scope,goal);
    const value=t.term(first.using,scope,null);
    const suppliedType=scope.infer(value).type;
    // A type is simplified as a whole and transported along; an equality at
    // its endpoints.
    const types=scope.nf(goal.target).tag!=="Path";
    const simplify=(subject,subset,fuel,describe)=>types
      ? t.simplifyTypeTerm(subject,subset,fuel,describe) : t.simplifyEqualityGoal(subject,subset,fuel,describe);
    // One fuel for both simplifications; the supplied term was elaborated
    // before it starts. A search that stops is described by its phase.
    const fuel=t.searchFuelAt(scope,"simpa");
    let supplied,target;
    try {
      try {supplied=simplify(goal.with(suppliedType),rules,fuel,false);}
      catch(error) {throw t.simpaStopped(error,"Simplifying the supplied type",null);}
      try {target=simplify(goal,rules,fuel,false);}
      catch(error) {throw t.simpaStopped(error,"Simplifying the goal",supplied);}
    } finally {fuel.close();}
    let checked;
    try {
      checked=t.checkSimplified(supplied.transition.forward(value),target.transition.next.target,
        scope,supplied.dependent||target.dependent);
    } catch(error) {
      if(typeof error?.message==="string")error.message+=` Simplifying the supplied type: ${
        t.rewriteSummary(supplied.transition.trace)} Simplifying the goal: ${t.rewriteSummary(target.transition.trace)}`;
      throw error;
    }
    const trace=[...supplied.transition.trace.map(step=>({...step,phase:types?"supplied":"supplied type"})),
      ...target.transition.trace.map(step=>({...step,phase:"goal"}))];
    return t.conclude(first,target.transition,checked,result=>({
      freeze:t.freezeSimplification(first,rules,trace,scope,(subset,at)=>{
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
  },
  intro(t,first,rest,goal) {
    const {scope}=goal;
    const pi=scope.nf(goal.target);
    if(pi.tag==="LPi") {
      // A universe variable, from a goal forall U < UU0. B.
      const {name,inner}=t.universeBinder(first.name,{kind:"name",name:"UU0"},scope);
      const next=new Goal(T.levelApply(T.levelLambda(pi.name,pi.body),T.variable(name)),inner);
      return new Transition(goal,next,[steps.abstraction(name,null)]).rebuild(t.block(rest,next));
    }
    if(pi.tag!=="Pi")throw Error("intro requires a dependent function goal.");
    const name=scope.fresh(first.name.text),variable=T.variable(name);
    const inner=t.sourceBinding(first.name,variable,scope.bind(name,pi.domain));
    const next=new Goal(T.app(T.lam(pi.name,pi.domain,pi.body),variable),inner);
    return new Transition(goal,next,[steps.abstraction(name,pi.domain)]).rebuild(t.block(rest,next));
  },
  hlevel(t,first,rest,goal) {
    const {scope}=goal;
    if(rest.length)throw Error("Statements after hlevel are unreachable.");
    return t.hlevel(first,goal,scope);
  },
  ext(t,first,rest,goal) {
    const {scope}=goal;
    const path=goal.equality();
    if(!path)throw Error("ext requires equality of functions with a fixed type.");
    const pi=scope.nf(path.family);
    if(pi.tag!=="Pi")throw Error("ext requires equality of functions.");
    const name=scope.fresh(first.variable.text),variable=T.variable(name);
    const inner=t.sourceBinding(first.variable,variable,scope.bind(name,pi.domain));
    const output=T.app(T.lam(pi.name,pi.domain,pi.body),variable);
    const next=new Goal(T.path(scope.fresh("i"),output,T.app(path.left,variable),T.app(path.right,variable)),inner);
    return new Transition(goal,next,[steps.congruence(name,pi.domain,path.family)]).rebuild(t.block(rest,next));
  },
  over(t,first,rest,goal) {
    const {scope}=goal;
    if(rest.length)throw Error("Statements after over are unreachable.");
    const target=scope.nf(goal.target);
    if(target.tag!=="Path")throw Error("over requires an expected PathP goal.");
    const C=t.term(first.family,scope,null),p=t.term(first.path,scope,null);
    const base=scope.nf(scope.infer(p).type);
    if(base.tag!=="Path"||freeDimensions(base.family).has(base.dim))
      throw Error("over requires a homogeneous base path.");
    const dim=scope.fresh("i"),family=T.app(C,T.at(p,I.variable(dim)));
    const transported=T.comp(dim,family,[],target.left);
    const fiber=T.app(C,base.right);
    const next=goal.with(T.path(scope.fresh("j"),fiber,transported,target.right));
    const transition=new Transition(goal,next,
      [steps.lemma(transportToDependentPath(dim,family,target.left,target.right),next.target)]);
    const result=transition.rebuild(t.block(first.body,next));
    scope.check(result,goal.target);
    return result;
  },
  let(t,first,rest,goal) {
    const {scope}=goal,{unit}=scope;
    if(first.target.kind!=="name")return undefined;
    // let name : T { … } proves a local lemma, and let name : T := term
    // checks a term against T. Either keeps T as the name's signature, as a
    // top-level proof does; the value stays visible to conversion.
    if(first.type) {
      const type=t.term(first.type,scope,null),sort=scope.infer(type).type;
      if(scope.nf(sort).tag!=="U")
        throw unit.locate(Error(`let states a type after the colon; found a value of type ${t.shown(sort)}.`),first.type);
      const checked=first.body?scope.check(t.block(first.body,new Goal(type,scope)),type)
        :scope.check(t.term(first.value,scope,type),type);
      return t.block(rest,goal.at(t.sourceBinding(first.target,scope.ascribe(checked,type),scope)));
    }
    const value=t.term(first.value,scope,null);
    scope.infer(value);
    return t.block(rest,goal.at(t.sourceBinding(first.target,value,scope)));
  },
  obtain(t,first,rest,goal) {
    const {scope}=goal;
    const value=t.term(first.value,scope,null);
    let inner=scope;
    const bind=(pattern,term)=>{
      if(pattern.kind==="name") {inner=t.sourceBinding(pattern,term,inner);return;}
      if(pattern.kind!=="pair"||scope.nf(scope.infer(term).type).tag!=="Sigma")
        throw Error("obtain requires a dependent pair matching its pattern.");
      bind(pattern.left,T.first(term));bind(pattern.right,T.second(term));
    };
    scope.infer(value);bind(first.target,value);
    return t.block(rest,goal.at(inner));
  },
  matchStatement(t,first,rest,goal) {
    const {scope}=goal;
    if(rest.length)throw Error("Statements after match are unreachable: each clause's block closes the goal.");
    return elaborateMatchStatement(t,first,goal,scope);
  },
  cases(t,first,rest,goal) {
    const {scope}=goal;
    if(rest.length)throw Error("Statements after cases are not yet translated.");
    const value=t.term(first.value,scope,null),type=scope.infer(value).type;
    const sum=scope.nf(type);
    if(sum.tag!=="Sum")throw Error("cases requires a sum type.");
    const motive=T.lam(scope.fresh(),type,goal.target);
    const branch=side=>{
      // Each branch's binder keeps its source name.
      const name=scope.fresh(first[side]?.text),domain=sum[side];
      const inner=t.sourceBinding(first[side],T.variable(name),scope.bind(name,domain));
      return T.lam(name,domain,t.block(first[side+"Body"],goal.at(inner)));
    };
    return T.sumrec(motive,branch("left"),branch("right"),value);
  },
};
