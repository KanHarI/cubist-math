import test from 'node:test';
import assert from 'node:assert/strict';
import {T,Checker} from '../core.mjs';
import {interval as I} from '../lattice.mjs';
import {checkNative} from '../native.mjs';
import {equiv,strictIsomorphismEquivalence} from '../equivalence.mjs';
import {halfAdjointEquiv,halfAdjointToNative,nativeToHalfAdjoint,
  publicUnivalencePath,publicUnivalenceBeta,nativeEquivalenceRoundTrip} from '../public-equivalence.mjs';
const v=T.variable;
function close(term,context,kind) {
  for(const [name,type]of [...context].reverse())term=kind(name,type,term);
  return term;
}
function checked(term,type,context) {
  term=close(term,context,T.lam);type=close(type,context,T.pi);
  const checker=new Checker({fuel:2000000});
  checker.check(term,checker.type(type,new Map(),new Set()).term,new Map(),new Set());
  const result=checkNative(term,type,[],{normalize:false});
  assert(result.ok,result.error);
  return result;
}
for(const level of [0,2]) {
  test(`native contractible fibers give public half-adjoint equivalences at U${level}`,()=>{
    const A=v('A'),B=v('B'),e=v('e');
    checked(nativeToHalfAdjoint(A,B,e),halfAdjointEquiv(A,B),
      [['A',T.universe(level)],['B',T.universe(level)],['e',equiv(A,B)]]);
  });
  test(`public half-adjoint equivalences supply native fibers at U${level}`,()=>{
    const A=v('A'),B=v('B'),e=v('e');
    checked(halfAdjointToNative(A,B,e),equiv(A,B),
      [['A',T.universe(level)],['B',T.universe(level)],['e',halfAdjointEquiv(A,B)]]);
  });
}
test('public ua and transport beta accept the exact half-adjoint representation',()=>{
  const A=v('A'),B=v('B'),e=v('e'),x=v('x');
  const context=[['A',T.universe(0)],['B',T.universe(0)],['e',halfAdjointEquiv(A,B)],['x',A]];
  const ua=publicUnivalencePath(A,B,e);
  checked(ua,T.path('i',T.universe(0),A,B),context);
  const transported=T.comp('i',T.at(ua,I.variable('i')),[],x);
  checked(publicUnivalenceBeta(A,B,e,x),T.path('j',B,transported,T.app(T.first(e),x)),context);
});

test('conversion round trip preserves the native equivalence',()=>{
  const A=v('A'),B=v('B'),e=v('e');
  const context=[['A',T.universe(0)],['B',T.universe(0)],['e',equiv(A,B)]];
  const term=close(nativeEquivalenceRoundTrip(A,B,e),context,T.lam);
  const type=close(T.path('i',equiv(A,B),halfAdjointToNative(A,B,nativeToHalfAdjoint(A,B,e)),e),context,T.pi);
  const result=checkNative(term,type,[],{normalize:false});
  assert(result.ok,result.error);
});
test('public ua moves a product by the supplied nonidentity forward map',()=>{
  const ref=name=>({tag:'Ref',name});
  const A=T.sigma('n',T.nat,T.unit),B=T.sigma('u',T.unit,T.nat);
  const f=T.lam('p',A,T.pair(B,T.second(v('p')),T.first(v('p'))));
  const g=T.lam('q',B,T.pair(A,T.second(v('q')),T.first(v('q'))));
  const definitions=[{name:'A',value:A},{name:'B',value:B},
    {name:'native',value:strictIsomorphismEquivalence(A,B,f,g)},
    {name:'public',value:nativeToHalfAdjoint(ref('A'),ref('B'),ref('native'))},
    {name:'ua',value:publicUnivalencePath(ref('A'),ref('B'),ref('public'))}];
  const x=T.pair(A,T.succ(T.zero),T.point);
  const moved=T.comp('i',T.at(ref('ua'),I.variable('i')),[],x);
  const result=checkNative(moved,B,[],{definitions});
  assert(result.ok,result.error);
  assert.deepEqual(result.normal.first,T.point);
  assert.deepEqual(result.normal.second,T.succ(T.zero));
  const beta=publicUnivalenceBeta(ref('A'),ref('B'),ref('public'),x);
  const bad=T.path('i',B,moved,T.pair(B,T.point,T.zero));
  assert.equal(checkNative(beta,bad,[],{definitions,normalize:false}).ok,false);
});
