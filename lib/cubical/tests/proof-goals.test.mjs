import test from 'node:test';
import assert from 'node:assert/strict';
import {Checker,T} from '../core.mjs';
import {Scope,SourceUnit} from '../elaboration.mjs';
import {Goal,Transition,steps,reflexivity,byConversion} from '../proof-goals.mjs';

// x y : Nat and p : x = y.
const x=T.variable('x'),y=T.variable('y'),p=T.variable('p');
const scope=()=>new Scope(new SourceUnit({checker:new Checker()}))
  .bind('x',T.nat).bind('y',T.nat).bind('p',T.path('i',T.nat,x,y));
const equal=(scope,left,right)=>new Goal(T.path(scope.fresh('i'),T.nat,left,right),scope);

test('a transition extends its plan without changing the transition it came from',()=>{
  const at=scope(),goal=equal(at,x,y);
  const start=new Transition(goal),next=goal.with(T.path('i',T.nat,y,y));
  const moved=start.extend(steps.composition(at,'lhs',p),next,{rule:'p'});
  assert.equal(start.next,goal);
  assert.deepEqual([start.plan.length,moved.plan.length,moved.trace.length],[0,1,1]);
  assert.equal(moved.goal,goal);
  assert.equal(moved.next,next);
  assert.ok(Object.isFrozen(goal)&&Object.isFrozen(start)&&Object.isFrozen(moved));
  assert.equal(goal.at(at.bind('z',T.nat)).target,goal.target);
});

test('rebuilding composes checked paths on either endpoint and forward reverses them',()=>{
  const at=scope();
  // x = y becomes y = y by p on the left.
  const left=new Transition(equal(at,x,y)).extend(steps.composition(at,'lhs',p),equal(at,y,y));
  const proof=left.rebuild(byConversion(left.next));
  assert.doesNotThrow(()=>at.check(proof,left.goal.target));
  assert.doesNotThrow(()=>at.check(left.forward(proof),left.next.target));
  // y = x becomes y = y by p on the right; the step keeps p's reversal.
  const step=steps.composition(at,'rhs',p);
  assert.ok(step.inverse);
  const right=new Transition(equal(at,y,x)).extend(step,equal(at,y,y));
  assert.doesNotThrow(()=>at.check(right.rebuild(reflexivity(right.next)),right.goal.target));
});

test('conversion closes only goals whose endpoints agree',()=>{
  const at=scope();
  assert.equal(byConversion(equal(at,x,y)),null);
  assert.equal(byConversion(new Goal(T.nat,at)),null);
  const proof=byConversion(equal(at,T.succ(x),T.succ(x)));
  assert.doesNotThrow(()=>at.check(proof,T.path('i',T.nat,T.succ(x),T.succ(x))));
});

test('a plan grants no proof authority: every rebuilt term is checked',()=>{
  const at=scope();
  // A composition whose witness does not reach the next goal's endpoint.
  const wrong=new Transition(equal(at,x,x)).extend(steps.composition(at,'lhs',p),equal(at,x,x));
  assert.throws(()=>wrong.rebuild(reflexivity(wrong.next)),/Path endpoints do not match/);
  // A lemma is applied only to a proof of its obligation.
  const lemma=T.lam('h',T.path('i',T.nat,x,y),T.variable('h'));
  const applied=new Transition(equal(at,x,y),equal(at,x,y),[steps.lemma(lemma,T.path('i',T.nat,x,y))]);
  assert.doesNotThrow(()=>at.check(applied.rebuild(p),applied.goal.target));
  assert.throws(()=>applied.rebuild(reflexivity(equal(at,x,x))));
});

test('binder steps rebuild functions and have no forward direction',()=>{
  const at=scope(),f=T.lam('n',T.nat,T.variable('n'));
  const inner=at.bind('n1',T.nat),n=T.variable('n1');
  const pointwise=new Goal(T.path('i',T.nat,T.app(f,n),T.app(f,n)),inner);
  const functions=T.path('i',T.pi('n',T.nat,T.nat),f,f);
  const ext=new Transition(new Goal(functions,at),pointwise,[steps.congruence('n1',T.nat,T.pi('n',T.nat,T.nat))]);
  assert.doesNotThrow(()=>at.check(ext.rebuild(reflexivity(pointwise)),functions));
  const intro=new Transition(new Goal(T.pi('n',T.nat,T.nat),at),new Goal(T.nat,inner),[steps.abstraction('n1',T.nat)]);
  assert.doesNotThrow(()=>at.check(intro.rebuild(n),T.pi('n',T.nat,T.nat)));
  assert.throws(()=>intro.forward(f),/abstraction step has no forward direction/);
});
