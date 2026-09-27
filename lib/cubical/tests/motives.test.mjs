import test from 'node:test';
import assert from 'node:assert/strict';
import {Checker,T} from '../core.mjs';
import {Scope,SourceUnit} from '../elaboration.mjs';
import {Goal,reflexivity} from '../proof-goals.mjs';
import {abstractMotive} from '../motives.mjs';

const at=(...bindings)=>bindings.reduce((scope,[name,type])=>scope.bind(name,type),
  new Scope(new SourceUnit({checker:new Checker()})));
const v=T.variable,path=(type,left,right)=>T.path('i',type,left,right);
const refl=(scope,type,value)=>reflexivity(new Goal(path(type,value,value),scope));

test('a hypothesis about the scrutinee is generalized and introduced again in each branch',()=>{
  // n : Nat, h : n = n, goal succ(n) = succ(n): induction on n.
  const scope=at(['n',T.nat],['h',path(T.nat,v('n'),v('n'))]);
  const goal=new Goal(path(T.nat,T.succ(v('n')),T.succ(v('n'))),scope);
  const motive=abstractMotive(goal,[v('n')]);
  assert.deepEqual(motive.generalized.map(hypothesis=>hypothesis.name),['h']);
  const branch=(value,inner)=>{
    const {transition,renamed}=motive.introduce(motive.instance([value],inner));
    assert.deepEqual([...renamed.keys()],['h']);
    // The hypothesis is about the constructor now, not about n.
    assert.ok(transition.next.scope.equal(transition.next.scope.context.get(renamed.get('h').name),
      path(T.nat,value,value)));
    return transition.rebuild(refl(transition.next.scope,T.nat,T.succ(value)));
  };
  const k=scope.fresh('k'),ih=scope.fresh('ih'),stepScope=scope.bind(k,T.nat);
  const step=T.lam(k,T.nat,T.lam(ih,T.app(motive.term,v(k)),
    branch(T.succ(v(k)),stepScope.bind(ih,T.app(motive.term,v(k))))));
  const proof=motive.apply(T.natrec(motive.term,branch(T.zero,scope),step,v('n')));
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
  const scope=at(['f',T.pi('m',T.nat,T.nat)],['n',T.nat]);
  const fn=T.app(v('f'),v('n'));
  // The second occurrence is about a bound n, not the scrutinee.
  const shadowed=T.pi('n',T.nat,path(T.nat,fn,fn));
  const goal=new Goal(T.sigma('s',path(T.nat,fn,fn),shadowed),scope);
  const motive=abstractMotive(goal,[fn]);
  const [y]=motive.binders;
  assert.ok(scope.bind(y.name,T.nat).equal(motive.instance([v(y.name)]).target,
    T.sigma('s',path(T.nat,v(y.name),v(y.name)),shadowed)));
  assert.ok(scope.equal(motive.instance([fn]).target,goal.target));
});

test('an unchanged goal keeps its identity and a scrutinee may not depend on a generalized hypothesis',()=>{
  const scope=at(['n',T.nat],['h',path(T.nat,v('n'),T.zero)],['q',path(path(T.nat,v('n'),T.zero),v('h'),v('h'))]);
  const one=T.succ(T.zero),goal=new Goal(path(T.nat,v('n'),v('n')),scope);
  const constant=abstractMotive(goal,[one]);
  assert.deepEqual([constant.generalized,constant.term.body],[[],goal.target]);
  assert.equal(constant.instance([T.zero]).target,goal.target);
  // h mentions n, so it is generalized; q, a scrutinee, is about h.
  assert.throws(()=>abstractMotive(new Goal(T.nat,scope),[v('n'),v('q')]),
    /A scrutinee depends on a hypothesis about another scrutinee/);
});
