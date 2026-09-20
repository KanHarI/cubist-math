import test from 'node:test';
import assert from 'node:assert/strict';
import {T,Checker} from '../core.mjs';
import {interval as I} from '../lattice.mjs';
import {pushout,suspension,north,south,meridian} from '../pushouts.mjs';
import {checkNative} from '../native.mjs';
const v=T.variable;
function checked(term,type) {
  const js=new Checker({fuel:1000000});
  const reference=js.verify(term,type);
  const native=checkNative(term,type);
  assert(native.ok,native.error);
  assert(js.equal(native.normal,reference.normal));
  js.verify(native.normal,type);
  assert(checkNative(native.normal,type,[],{normalize:false}).ok);
  return native;
}

test('suspension is a derived pushout with computational meridian endpoints',()=>{
  const A=T.sum(T.unit,T.unit),P=suspension(A),a=T.inl(A,T.point);
  checked(P,T.universe(0));
  checked(meridian(A,a),T.path('i',P,north(A),south(A)));
  assert.equal(checked(T.at(meridian(A,a),I.zero),P).normal.tag,'PushLeft');
  assert.equal(checked(T.at(meridian(A,a),I.one),P).normal.tag,'PushRight');
});

test('pushout dependent elimination computes on point and bridge constructors',()=>{
  const f=T.lam('n',T.nat,T.succ(v('n'))),g=T.lam('n',T.nat,T.zero);
  const P=pushout(T.nat,T.nat,T.nat,f,g);
  const motive=T.lam('z',P,T.path('j',P,v('z'),v('z')));
  const left=T.lam('a',T.nat,T.line('j',P,T.pushLeft(P,v('a'))));
  const right=T.lam('b',T.nat,T.line('j',P,T.pushRight(P,v('b'))));
  const bridge=T.lam('c',T.nat,T.line('i',T.app(motive,T.pushPath(P,v('c'),I.variable('i'))),
    T.line('j',P,T.pushPath(P,v('c'),I.variable('i')))));
  const elim=T.pushElim(motive,left,right,bridge);
  checked(elim,T.pi('z',P,T.app(motive,v('z'))));
  checked(T.app(elim,T.pushLeft(P,T.zero)),T.app(motive,T.pushLeft(P,T.zero)));
  const line=T.line('i',T.app(motive,T.pushPath(P,T.zero,I.variable('i'))),
    T.app(elim,T.pushPath(P,T.zero,I.variable('i'))));
  checked(line,T.path('i',T.app(motive,T.pushPath(P,T.zero,I.variable('i'))),
    T.app(left,T.succ(T.zero)),T.app(right,T.zero)));
  const wrong=T.lam('c',T.nat,T.line('i',T.app(motive,T.pushPath(P,v('c'),I.variable('i'))),
    T.line('j',P,T.pushLeft(P,v('c')))));
  assert.equal(checkNative(T.pushElim(motive,left,right,wrong),null,[],{normalize:false}).ok,false);
});
