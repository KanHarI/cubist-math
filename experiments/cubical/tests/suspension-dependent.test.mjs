import test from 'node:test';
import assert from 'node:assert/strict';
import {Checker,T} from '../core.mjs';
import {interval as I} from '../lattice.mjs';
import {suspension,north,south} from '../pushouts.mjs';
import {transportToDependentPath} from '../path-over.mjs';
import {checkNative} from '../native.mjs';

const v=T.variable;

function eliminator(A,motive,northValue,southValue,meridians,{dependent=true}={}) {
  const P=suspension(A),a=v('a'),u=v('u'),point=v('point');
  const family=T.app(motive,T.pushPath(P,a,I.variable('i')));
  const bridge=T.lam('a',A,T.app(
    transportToDependentPath('i',family,northValue,southValue),T.app(meridians,a)));
  const branch=(constructor,value)=>T.lam('u',T.unit,dependent
    ?T.unitrec(T.lam('point',T.unit,T.app(motive,constructor(P,point))),value,u)
    :value);
  return T.pushElim(motive,branch(T.pushLeft,northValue),branch(T.pushRight,southValue),bridge);
}

for(const level of [0,2])test(`suspension dependent point branches use Unit elimination at U${level}`,()=>{
  const A=v('A'),P=suspension(A),motive=v('motive'),n=v('northValue'),s=v('southValue');
  const family=T.app(motive,T.pushPath(P,v('a'),I.variable('i')));
  const moved=T.comp('i',family,[],n);
  const assumptions=[['A',T.universe(0)],['motive',T.pi('x',P,T.universe(level))],
    ['northValue',T.app(motive,north(A))],['southValue',T.app(motive,south(A))],
    ['meridians',T.pi('a',A,T.path('j',T.app(motive,south(A)),moved,s))]];
  const result=eliminator(A,motive,n,s,v('meridians'));
  const expected=T.pi('x',P,T.app(motive,v('x')));
  new Checker().verify(result,expected,assumptions);
  const native=checkNative(result,expected,assumptions,{normalize:false});
  assert(native.ok,native.error);
  for(const [point,value] of [[north(A),n],[south(A),s]]) {
    const computation=T.line('j',T.app(motive,point),T.app(result,point));
    const type=T.path('j',T.app(motive,point),value,value);
    const checked=checkNative(computation,type,assumptions,{normalize:false});
    assert(checked.ok,checked.error);
  }
  // Unit has one constructor, but a neutral u is not judgmentally tt. Thus a
  // fixed pole value cannot inhabit motive(push_left u) without elimination.
  const invalid=eliminator(A,motive,n,s,v('meridians'),{dependent:false});
  assert.throws(()=>new Checker().verify(invalid,expected,assumptions));
  assert.equal(checkNative(invalid,expected,assumptions,{normalize:false}).ok,false);
});
