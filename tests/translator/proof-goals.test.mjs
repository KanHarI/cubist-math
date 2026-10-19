import "../fresh-build.mjs";
import test from 'node:test';
import assert from 'node:assert/strict';
import {T} from '../../web/translator/core.mjs';
import {Scope,SourceUnit} from '../../web/translator/elaboration.mjs';
import {Goal,Transition,steps,reflexivity,byConversion,composePaths,transportTypePath} from '../../web/translator/proof-goals.mjs';
import {equalityRule} from '../../web/translator/proof-rewrite.mjs';
import {Translator} from '../../web/translator/translate.mjs';
import {builtinTerm} from '../../web/translator/builtins.mjs';

import {kernelChecker} from './kernel-check.mjs';
// Two points, the examples' small inductive type.
const two=T.sum(T.unit,T.unit);
// f : two -> two, x y : two and p : x = y.
const x=T.variable('x'),y=T.variable('y'),p=T.variable('p'),f=value=>T.app(T.variable('f'),value);
const checkedScope=t=>{
  const checker=kernelChecker();
  t.after(()=>checker.kernel.dispose());
  return new Scope(new SourceUnit({checker}));
};
const scope=t=>checkedScope(t)
  .bind('f',T.pi('n',two,two)).bind('x',two).bind('y',two).bind('p',T.path('i',two,x,y));
const equal=(scope,left,right)=>new Goal(T.path(scope.fresh('i'),two,left,right),scope);

test('a transition extends its plan without changing the transition it came from',t=>{
  const at=scope(t),goal=equal(at,x,y);
  const start=new Transition(goal),next=goal.with(T.path('i',two,y,y));
  const moved=start.extend(steps.composition(at,'lhs',p),next,{rule:'p'});
  assert.equal(start.next,goal);
  assert.deepEqual([start.plan.length,moved.plan.length,moved.trace.length],[0,1,1]);
  assert.equal(moved.goal,goal);
  assert.equal(moved.next,next);
  assert.ok(Object.isFrozen(goal)&&Object.isFrozen(start)&&Object.isFrozen(moved));
  assert.equal(goal.at(at.bind('z',two)).target,goal.target);
});

test('rebuilding composes checked paths on either endpoint and forward reverses them',t=>{
  const at=scope(t);
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

test('conversion closes only goals whose endpoints agree',t=>{
  const at=scope(t);
  assert.equal(byConversion(equal(at,x,y)),null);
  assert.equal(byConversion(new Goal(two,at)),null);
  const proof=byConversion(equal(at,f(x),f(x)));
  assert.doesNotThrow(()=>at.check(proof,T.path('i',two,f(x),f(x))));
});

test('a plan grants no proof authority: every rebuilt term is checked',t=>{
  const at=scope(t);
  // A composition whose witness does not reach the next goal's endpoint.
  const wrong=new Transition(equal(at,x,x)).extend(steps.composition(at,'lhs',p),equal(at,x,x));
  assert.throws(()=>wrong.rebuild(reflexivity(wrong.next)),/Path endpoints do not match/);
  // A lemma is applied only to a proof of its obligation.
  const lemma=T.lam('h',T.path('i',two,x,y),T.variable('h'));
  const applied=new Transition(equal(at,x,y),equal(at,x,y),[steps.lemma(lemma,T.path('i',two,x,y))]);
  assert.doesNotThrow(()=>at.check(applied.rebuild(p),applied.goal.target));
  assert.throws(()=>applied.rebuild(reflexivity(equal(at,x,x))));
});

test('binder steps rebuild functions and have no forward direction',t=>{
  const at=scope(t),f=T.lam('n',two,T.variable('n'));
  const inner=at.bind('n1',two),n=T.variable('n1');
  const pointwise=new Goal(T.path('i',two,T.app(f,n),T.app(f,n)),inner);
  const functions=T.path('i',T.pi('n',two,two),f,f);
  const ext=new Transition(new Goal(functions,at),pointwise,[steps.congruence('n1',two,T.pi('n',two,two))]);
  assert.doesNotThrow(()=>at.check(ext.rebuild(reflexivity(pointwise)),functions));
  const intro=new Transition(new Goal(T.pi('n',two,two),at),new Goal(two,inner),[steps.abstraction('n1',two)]);
  assert.doesNotThrow(()=>at.check(intro.rebuild(n),T.pi('n',two,two)));
  assert.throws(()=>intro.forward(f),/abstraction step has no forward direction/);
});

test('equality goals reduce ignored motive arguments, including beneath another path',t=>{
  const at=scope(t);
  const family=T.app(T.lam('ignored',two,two),T.at(p,[['i:1']]));
  const line=T.line('j',two,x);
  for(const target of [T.path('i',family,x,x),T.path('i',T.path('j',family,x,x),line,line)]) {
    const goal=new Goal(target,at),proof=byConversion(goal);
    assert.ok(proof,'a beta-constant family is a homogeneous equality goal');
    assert.doesNotThrow(()=>at.check(proof,target));
  }
});

test('reducing a motive that uses its argument preserves genuine dependence',t=>{
  const at=checkedScope(t)
    .bind('A',T.universe(0)).bind('B',T.universe(0))
    .bind('e',T.path('j',T.universe(0),T.variable('A'),T.variable('B')))
    .bind('a',T.variable('A')).bind('b',T.variable('B'));
  const family=T.app(T.lam('X',T.universe(0),T.variable('X')),T.at(T.variable('e'),[['i:1']]));
  const target=T.path('i',family,T.variable('a'),T.variable('b'));
  assert.equal(new Goal(target,at).equality(),null);
  const inner=at.bind('dependent',target),p=T.variable('dependent');
  const translator=new Translator({checker:inner.checker});
  assert.throws(()=>translator.reversePath(inner,p,'sym'),/sym requires a path/);
  assert.throws(()=>translator.concatenatePaths(inner,p,p,'trans'),/trans requires paths/);
  assert.throws(()=>equalityRule(inner,p),/homogeneous equality/);
});

test('path witnesses reduce ignored arguments before their family leaves its binder',t=>{
  const family=T.app(T.lam('ignored',two,two),T.at(p,[['bound:1']]));
  const at=scope(t).bind('h',T.path('bound',family,x,y)),h=T.variable('h');
  const translator=new Translator({checker:at.checker});
  const forwards=T.path('j',two,x,y),backwards=T.path('j',two,y,x);
  assert.doesNotThrow(()=>at.check(equalityRule(at,h).term,forwards));
  const reversed=equalityRule(at,h,true).term;
  assert.doesNotThrow(()=>at.check(reversed,backwards));
  assert.doesNotThrow(()=>at.check(composePaths(at,h,reversed),T.path('j',two,x,x)));
  for(const spelling of ['sym','~'])
    assert.doesNotThrow(()=>at.check(translator.reversePath(at,h,spelling),backwards));
  for(const spelling of ['trans','++'])
    assert.doesNotThrow(()=>at.check(translator.concatenatePaths(at,h,reversed,spelling),T.path('j',two,x,x)));
  // Supply raw, already checked arguments to the builtin's normal handler.
  const motive=T.lam('a',two,T.lam('b',two,T.lam('q',T.path('j',two,T.variable('a'),T.variable('b')),T.unit)));
  const base=T.lam('a',two,T.point);
  const induction=builtinTerm({term:term=>term},'path_induction',{args:[two,motive,base,x,y,h]},at,null);
  assert.doesNotThrow(()=>at.check(induction,T.unit));
});

test('type-path transport recognizes a beta-constant universe family',t=>{
  const at=scope(t).bind('A',T.universe(0)).bind('B',T.universe(0));
  const family=T.app(T.lam('ignored',two,T.universe(0)),T.at(p,[['bound:1']]));
  const inner=at.bind('types',T.path('bound',family,T.variable('A'),T.variable('B'))).bind('a',T.variable('A'));
  const moved=transportTypePath(inner,T.variable('types'),T.variable('a'));
  assert.doesNotThrow(()=>inner.check(moved,T.variable('B')));
});
