import test from 'node:test';
import assert from 'node:assert/strict';
import {T,Checker} from '../core.mjs';
import {checkNative} from '../native.mjs';
import {pathInverse,pathApply,pathConcat} from '../path-algebra.mjs';
import {cancelRight,prependInverseCancel,homotopyNatural,homotopySelf,applyInterchange} from '../adjointification.mjs';
const v=T.variable,app=T.app,eq=(A,x,y)=>T.path('i',A,x,y);
function close(term,context,kind) {
  for(const [name,type]of [...context].reverse())term=kind(name,type,term);
  return term;
}
function checked(term,type,context,reference=true) {
  term=close(term,context,T.lam);type=close(type,context,T.pi);
  if(reference) {
    const checker=new Checker({fuel:2000000});
    checker.check(term,checker.type(type,new Map(),new Set()).term,new Map(),new Set());
  }
  const result=checkNative(term,type,[],{normalize:false});
  assert(result.ok,result.error);
  return result;
}
test('right cancellation and prepend inverse cancellation use the canonical concat',()=>{
  const A=v('A'),x=v('x'),y=v('y'),z=v('z'),p=v('p'),q=v('q'),r=v('r'),h=v('h');
  const context=[['A',T.universe(1)],['x',A],['y',A],['z',A],['p',eq(A,x,y)],
    ['q',eq(A,x,y)],['r',eq(A,y,z)],['h',eq(eq(A,x,z),pathConcat(A,x,p,r),pathConcat(A,x,q,r))]];
  checked(cancelRight(A,x,y,z,p,q,r,h),eq(eq(A,x,y),p,q),context);
  checked(prependInverseCancel(A,x,y,z,p,r),eq(eq(A,y,z),
    pathConcat(A,y,pathInverse(A,p),pathConcat(A,x,p,r)),r),context);
});
for(const level of [0,2])test(`homotopy naturality and self-naturality at U${level}`,()=>{
  const A=v('A'),f=v('f'),h=v('h'),x=v('x'),y=v('y'),p=v('p');
  const context=[['A',T.universe(level)],['f',T.pi('a',A,A)],
    ['h',T.pi('a',A,eq(A,app(f,v('a')),v('a')))],['x',A],['y',A],['p',eq(A,x,y)]];
  checked(homotopyNatural(A,f,h,x,y,p),eq(eq(A,app(f,x),y),
    pathConcat(A,app(f,x),pathApply(A,f,p),app(h,y)),
    pathConcat(A,app(f,x),app(h,x),p)),context);
  checked(homotopySelf(A,f,h,x),eq(eq(A,app(f,app(f,x)),app(f,x)),
    pathApply(A,f,app(h,x)),app(h,app(f,x))),context);
});
test('ap interchange is definitional for direct cubical application',()=>{
  const A=v('A'),B=v('B'),f=v('f'),g=v('g'),x=v('x'),y=v('y'),p=v('p');
  const context=[['A',T.universe(0)],['B',T.universe(2)],['f',T.pi('a',A,B)],
    ['g',T.pi('b',B,A)],['x',A],['y',A],['p',eq(A,x,y)]];
  const gf=T.lam('a',A,app(g,app(f,v('a')))),fg=T.lam('b',B,app(f,app(g,v('b'))));
  checked(applyInterchange(A,B,f,g,x,y,p),eq(eq(B,app(f,app(g,app(f,x))),app(f,app(g,app(f,y)))),
    pathApply(B,f,pathApply(A,gf,p)),pathApply(B,fg,pathApply(B,f,p))),context);
});
