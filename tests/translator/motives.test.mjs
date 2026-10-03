import "../fresh-build.mjs";
import test from 'node:test';
import assert from 'node:assert/strict';
import {T} from '../../web/translator/core.mjs';
import {Scope,SourceUnit} from '../../web/translator/elaboration.mjs';
import {Goal,reflexivity} from '../../web/translator/proof-goals.mjs';
import {abstractMotive} from '../../web/translator/motives.mjs';
import {kernelChecker} from './kernel-check.mjs';
// Two points, the examples' small inductive type.
const two=T.sum(T.unit,T.unit);

const at=(...bindings)=>bindings.reduce((scope,[name,type])=>scope.bind(name,type),
  new Scope(new SourceUnit({checker:kernelChecker()})));
const v=T.variable,path=(type,left,right)=>T.path('i',type,left,right);
const refl=(scope,type,value)=>reflexivity(new Goal(path(type,value,value),scope));

test('a hypothesis about the scrutinee is generalized and introduced again in each branch',()=>{
  // f : two -> two, n : two, h : n = n, goal f(n) = f(n): case analysis on n.
  const scope=at(['f',T.pi('x',two,two)],['n',two],['h',path(two,v('n'),v('n'))]);
  const f=value=>T.app(v('f'),value);
  const goal=new Goal(path(two,f(v('n')),f(v('n'))),scope);
  const motive=abstractMotive(goal,[v('n')]);
  assert.deepEqual(motive.generalized.map(hypothesis=>hypothesis.name),['h']);
  const branch=(value,inner)=>{
    const {transition,renamed}=motive.introduce(motive.instance([value],inner));
    assert.deepEqual([...renamed.keys()],['h']);
    // The hypothesis is about the constructor now, not about n.
    assert.ok(transition.next.scope.equal(transition.next.scope.context.get(renamed.get('h').name),
      path(two,value,value)));
    return transition.rebuild(refl(transition.next.scope,two,f(value)));
  };
  const u=scope.fresh('u'),inner=scope.bind(u,T.unit);
  const proof=motive.apply(T.sumrec(motive.term,
    T.lam(u,T.unit,branch(T.inl(two,v(u)),inner)),T.lam(u,T.unit,branch(T.inr(two,v(u)),inner)),v('n')));
  assert.doesNotThrow(()=>scope.check(proof,goal.target));
});

test('several scrutinees are bound in order, so a later type can mention an earlier one',()=>{
  // Based path induction's motive: x and p : x = a, abstracted together.
  const scope=at(['A',T.universe(0)],['a',v('A')],['x',v('A')],['p',path(v('A'),v('x'),v('a'))]);
  const goal=new Goal(path(path(v('A'),v('x'),v('a')),v('p'),v('p')),scope);
  const motive=abstractMotive(goal,[v('x'),v('p')]);
  const [x,p]=motive.binders;
  assert.ok(scope.bind(x.name,x.type).equal(p.type,path(v('A'),v(x.name),v('a'))));
  assert.deepEqual(motive.generalized,[]);
  // At the scrutinees themselves the motive is the goal again.
  assert.ok(scope.equal(motive.instance([v('x'),v('p')]).target,goal.target));
  const base=T.line('j',v('A'),v('a'));
  assert.ok(scope.equal(motive.instance([v('a'),base]).target,path(path(v('A'),v('a'),v('a')),base,base)));
});

test('a compound scrutinee is abstracted where it occurs, except under a binder of its names',()=>{
  const scope=at(['f',T.pi('m',two,two)],['n',two]);
  const fn=T.app(v('f'),v('n'));
  // The second occurrence is about a bound n, not the scrutinee.
  const shadowed=T.pi('n',two,path(two,fn,fn));
  const goal=new Goal(T.sigma('s',path(two,fn,fn),shadowed),scope);
  const motive=abstractMotive(goal,[fn]);
  const [y]=motive.binders;
  assert.ok(scope.bind(y.name,two).equal(motive.instance([v(y.name)]).target,
    T.sigma('s',path(two,v(y.name),v(y.name)),shadowed)));
  assert.ok(scope.equal(motive.instance([fn]).target,goal.target));
});

test('an unchanged goal keeps its identity and a scrutinee may not depend on a generalized hypothesis',()=>{
  const zero=T.inl(two,T.point),one=T.inr(two,T.point);
  const scope=at(['n',two],['h',path(two,v('n'),zero)],['q',path(path(two,v('n'),zero),v('h'),v('h'))]);
  const goal=new Goal(path(two,v('n'),v('n')),scope);
  const constant=abstractMotive(goal,[one]);
  assert.deepEqual([constant.generalized,constant.term.body],[[],goal.target]);
  assert.equal(constant.instance([zero]).target,goal.target);
  // h mentions n, so it is generalized; q, a scrutinee, is about h.
  assert.throws(()=>abstractMotive(new Goal(two,scope),[v('n'),v('q')]),
    /A scrutinee depends on a hypothesis about another scrutinee/);
});
