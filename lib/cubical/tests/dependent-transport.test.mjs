import test from 'node:test';
import assert from 'node:assert/strict';
import {T,Checker} from '../core.mjs';
import {checkNative} from '../native.mjs';
import {strictIsomorphismEquivalence,univalencePath} from '../equivalence.mjs';
import {pathRefl,pathInverse,pathApply,pathConcat,transportConstant} from '../path-algebra.mjs';
import {pathTransport,transportInverseAfter,transportAfterInverse,transportConcat,
  transportApply,transportDecoder,dependentApply,dependentApplyConstant,cancelLeft,appendCancelInverse,appendInverseCancel} from '../dependent-transport.mjs';
const v=T.variable,app=T.app;
const eq=(A,x,y)=>T.path('i',A,x,y);
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
  test(`dependent transport compositions and round trips at U${level}`,()=>{
    const A=v('A'),C=v('C'),x=v('x'),y=v('y'),z=v('z'),p=v('p'),q=v('q');
    const value=v('value'),last=v('last');
    const context=[['A',T.universe(level)],['C',T.pi('a',A,T.universe(level))],
      ['x',A],['y',A],['z',A],['p',eq(A,x,y)],['q',eq(A,y,z)],
      ['value',app(C,x)],['last',app(C,y)]];
    checked(transportInverseAfter(A,C,x,y,p,value),eq(app(C,x),
      pathTransport(C,pathInverse(A,p),pathTransport(C,p,value)),value),context);
    checked(transportAfterInverse(A,C,x,y,p,last),eq(app(C,y),
      pathTransport(C,p,pathTransport(C,pathInverse(A,p),last)),last),context);
    checked(transportConcat(A,C,x,y,z,p,q,value),eq(app(C,z),
      pathTransport(C,pathConcat(A,x,p,q),value),pathTransport(C,q,pathTransport(C,p,value))),context);
    const identity=T.lam('type',T.universe(level),v('type'));
    checked(transportApply(C,p,value),eq(app(C,y),pathTransport(C,p,value),
      pathTransport(identity,pathApply(T.universe(level),C,p),value)),context);
  });
}
test('decoder transport is computed by Pi and Path composition',()=>{
  const A=v('A'),C=v('C'),origin=v('origin'),x=v('x'),y=v('y'),p=v('p'),f=v('f'),value=v('value');
  const decoder=point=>T.pi('arg',app(C,point),eq(A,origin,point));
  const context=[['A',T.universe(1)],['C',T.pi('a',A,T.universe(0))],['origin',A],
    ['x',A],['y',A],['p',eq(A,x,y)],['f',decoder(x)],['value',app(C,y)]];
  const lhs=app(pathTransport(T.lam('point',A,decoder(v('point'))),p,f),value);
  const backwards=pathTransport(C,pathInverse(A,p),value);
  const rhs=pathConcat(A,origin,app(f,backwards),p);
  checked(transportDecoder(A,origin,C,x,y,p,f,value),eq(eq(A,origin,y),lhs,rhs),context);
});
test('dependent application into a constant family agrees with constant transport then ap',()=>{
  const A=v('A'),B=v('B'),f=v('f'),x=v('x'),y=v('y'),p=v('p');
  const context=[['A',T.universe(1)],['B',T.universe(2)],['f',T.pi('a',A,B)],
    ['x',A],['y',A],['p',eq(A,x,y)]];
  const C=T.lam('a',A,B),start=pathTransport(C,p,app(f,x));
  const lhs=dependentApply(C,f,x,y,p);
  const rhs=pathConcat(B,start,transportConstant(B,app(f,x)),pathApply(B,f,p));
  checked(dependentApplyConstant(A,B,f,x,y,p),eq(eq(B,start,app(f,y)),lhs,rhs),context);
});
test('left cancellation follows from the checked cubical groupoid laws',()=>{
  const A=v('A'),x=v('x'),y=v('y'),z=v('z'),p=v('p'),q=v('q'),r=v('r'),same=v('same');
  const context=[['A',T.universe(1)],['x',A],['y',A],['z',A],['p',eq(A,x,y)],
    ['q',eq(A,y,z)],['r',eq(A,y,z)],['same',eq(eq(A,x,z),pathConcat(A,x,p,q),pathConcat(A,x,p,r))]];
  checked(cancelLeft(A,x,y,z,p,q,r,same),eq(eq(A,y,z),q,r),context);
});

test('both forms of appended inverse cancellation preserve the prefix',()=>{
  const A=v('A'),x=v('x'),y=v('y'),z=v('z'),p=v('p'),q=v('q');
  const context=[['A',T.universe(1)],['x',A],['y',A],['z',A],['p',eq(A,x,y)],['q',eq(A,y,z)]];
  const lhs=pathConcat(A,x,pathConcat(A,x,p,q),pathInverse(A,q));
  checked(appendCancelInverse(A,x,y,z,p,q),eq(eq(A,x,y),lhs,p),context);
  const backwards=pathInverse(A,q);
  checked(appendInverseCancel(A,x,y,z,p,backwards),eq(eq(A,x,y),lhs,p),context);
});

test('dependent transport inverse law checks on a nonidentity Glue family',()=>{
  const ref=name=>({tag:'Ref',name});
  const A=T.sigma('n',T.nat,T.unit),B=T.sigma('u',T.unit,T.nat);
  const f=T.lam('p',A,T.pair(B,T.second(v('p')),T.first(v('p'))));
  const g=T.lam('q',B,T.pair(A,T.second(v('q')),T.first(v('q'))));
  const definitions=[{name:'A',value:A},{name:'B',value:B},
    {name:'e',value:strictIsomorphismEquivalence(A,B,f,g)},
    {name:'ua',value:univalencePath(ref('A'),ref('B'),ref('e'))},
    {name:'value',value:T.pair(A,T.succ(T.zero),T.point)}];
  const universe=T.universe(0),C=T.lam('type',universe,v('type'));
  const p=ref('ua'),value=ref('value');
  const lhs=pathTransport(C,pathInverse(universe,p),pathTransport(C,p,value));
  const proof=transportInverseAfter(universe,C,ref('A'),ref('B'),p,value);
  const result=checkNative(proof,eq(ref('A'),lhs,value),[],{definitions,normalize:false});
  assert(result.ok,result.error);
  assert(result.arenaNodes<50000);
  assert.equal(checkNative(proof,eq(ref('A'),lhs,T.pair(A,T.zero,T.point)),[],
    {definitions,normalize:false}).ok,false);
});
