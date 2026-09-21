import test from 'node:test';
import assert from 'node:assert/strict';
import {T,Checker} from '../core.mjs';
import {interval as I,face as F} from '../lattice.mjs';
import {pushout,suspension,north,south,meridian} from '../pushouts.mjs';
import {univalencePath,strictIsomorphismEquivalence} from '../equivalence.mjs';
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

test('canonical homogeneous composition has checked boundaries and dependent elimination',()=>{
  const P=suspension(T.unit),n=north(T.unit),s=south(T.unit);
  const motive=T.lam('z',P,T.path('j',P,v('z'),v('z')));
  const left=T.lam('a',T.unit,T.line('j',P,T.pushLeft(P,v('a'))));
  const right=T.lam('b',T.unit,T.line('j',P,T.pushRight(P,v('b'))));
  const bridge=T.lam('c',T.unit,T.line('i',T.app(motive,T.pushPath(P,v('c'),I.variable('i'))),
    T.line('j',P,T.pushPath(P,v('c'),I.variable('i')))));
  const elim=T.pushElim(motive,left,right,bridge);
  const box=T.hcomp('i',P,[
    {face:F.endpoint('r',0),term:T.pushPath(P,T.point,I.variable('i'))},
    {face:F.endpoint('r',1),term:n},
  ],n);
  checked(T.line('r',P,box),T.path('r',P,s,n));
  checked(T.line('r',T.app(motive,box),T.app(elim,box)),
    T.path('r',T.app(motive,box),T.app(right,T.point),T.app(left,T.point)));
  assert.equal(checked(T.hcomp('i',P,[],n),P).normal.tag,'HComp');
  const bad=T.hcomp('i',P,[{face:F.top,term:s}],n);
  assert.equal(checkNative(bad,P,[],{normalize:false}).ok,false);
});

test('transport across a changing span corrects both bridge endpoints',()=>{
  const C=suspension(T.unit),g=T.lam('x',T.unit,T.point);
  const family=r=>pushout(T.unit,C,T.unit,T.lam('x',T.unit,T.pushPath(C,T.point,r)),g);
  const old=family(I.zero),last=family(I.one);
  const source=T.pushPath(old,T.point,I.variable('r'));
  const moved=T.line('r',last,T.trans('i',family(I.variable('i')),F.bottom,source));
  const left=T.pushLeft(last,T.comp('i',C,[],north(T.unit))),right=T.pushRight(last,T.point);
  const expected=T.path('r',last,left,right);
  const result=checked(moved,expected);
  assert.equal(result.normal.body.tag,'HComp');
  // Without the correction this bridge starts at the OTHER pole of C.
  const uncorrected=T.line('r',last,T.pushPath(last,T.point,I.variable('r')));
  assert.equal(checkNative(uncorrected,expected,[],{normalize:false}).ok,false);
  // A claimed constant transport face is a premise, not trusted metadata.
  const wrong=T.trans('i',family(I.variable('i')),F.top,T.pushLeft(old,north(T.unit)));
  assert.equal(checkNative(wrong,last,[],{normalize:false}).ok,false);
});

test('HComp keeps its type in the outer cube and unsupported families are rejected',()=>{
  const C=suspension(T.unit),g=T.lam('x',T.unit,T.point);
  const family=r=>pushout(T.unit,C,T.unit,T.lam('x',T.unit,T.pushPath(C,T.point,r)),g);
  const P=family(I.variable('r'));
  // The inner r binds tube terms only; P's r belongs to the outer path.
  const body=T.hcomp('r',P,[],T.pushLeft(P,north(T.unit)));
  checked(T.line('r',P,body),null);
  assert.equal(checkNative(T.hcomp('i',T.nat,[],T.zero),T.nat,[],{normalize:false}).ok,false);
  assert.equal(checkNative(T.trans('i',T.nat,F.bottom,T.zero),T.nat,[],{normalize:false}).ok,false);
});

test('pushout transport supports changing carrier types through computational univalence',()=>{
  const A=T.sigma('n',T.nat,T.unit),B=T.sigma('u',T.unit,T.nat);
  const f=T.lam('p',A,T.pair(B,T.second(v('p')),T.first(v('p'))));
  const g=T.lam('q',B,T.pair(A,T.second(v('q')),T.first(v('q'))));
  const ua=univalencePath(A,B,strictIsomorphismEquivalence(A,B,f,g));
  const uaType=T.path('i',T.universe(0),A,B);
  const span=Q=>{const id=T.lam('x',Q,v('x'));return pushout(Q,Q,Q,id,id);};
  const P=span(A),Q=span(B),carrier=T.at(v('ua'),I.variable('i'));
  const a=T.pair(A,T.zero,T.point),b=T.pair(B,T.point,T.zero);
  const line=T.line('r',Q,T.trans('i',span(carrier),F.bottom,T.pushPath(P,a,I.variable('r'))));
  const moved=T.comp('i',carrier,[],a);
  const genericType=T.path('r',Q,T.pushLeft(Q,moved),T.pushRight(Q,moved));
  const reference=new Checker({fuel:1000000}),ctx=new Map([['ua',uaType]]);
  reference.check(line,reference.type(genericType,ctx,new Set()).term,ctx,new Set());
  const referenceNode=t=>Array.isArray(t)?t.map(referenceNode):t&&typeof t==='object'?
    t.tag==='Var'&&t.name==='ua'?{tag:'Ref',name:'ua'}:
    Object.fromEntries(Object.entries(t).map(([k,v])=>[k,referenceNode(v)])):t;
  // Native registration checks the actual Glue equivalence, so the closed
  // result has no universe-path assumption. Its endpoints are concrete b.
  const result=checkNative(referenceNode(line),T.path('r',Q,T.pushLeft(Q,b),T.pushRight(Q,b)),[],{
    definitions:[{name:'ua',value:ua,type:uaType}],normalize:false});
  assert(result.ok,result.error);
  assert(result.arenaNodes<100000);
});

test('transport remains fixed on a nontrivial constant face',()=>{
  const C=suspension(T.unit),g=T.lam('x',T.unit,T.point);
  const span=r=>pushout(T.unit,C,T.unit,T.lam('x',T.unit,T.pushPath(C,T.point,r)),g);
  const old=span(I.zero),target=span(I.variable('s'));
  const family=span(I.meet(I.variable('i'),I.variable('s')));
  const source=T.pushPath(old,T.point,I.variable('r'));
  const body=T.line('r',target,T.trans('i',family,F.endpoint('s',0),source));
  // Endpoint expressions may be inferred here: the s=0 face is the original
  // bridge, while the other face contains the corrected transported bridge.
  const outer=T.line('s',T.path('r',target,
    T.trans('i',family,F.endpoint('s',0),T.pushLeft(old,north(T.unit))),
    T.trans('i',family,F.endpoint('s',0),T.pushRight(old,T.point))),body);
  checked(outer,null);
  const fixed=checked(T.at(outer,I.zero),null);
  assert.equal(fixed.normal.body.tag,'PushPath');
});

test('pushouts preserve the maximum carrier universe and reject wrongly typed span maps',()=>{
  for(const level of [0,2]) {
    const statement=T.pi('A',T.universe(level),T.universe(level));
    checked(T.lam('A',T.universe(level),suspension(v('A'))),statement);
  }
  const wrong=pushout(T.unit,T.unit,T.unit,T.lam('x',T.unit,T.zero),T.lam('x',T.unit,T.point));
  assert.equal(checkNative(wrong,null,[],{normalize:false}).ok,false);
  assert.throws(()=>new Checker().verify(wrong));
});
