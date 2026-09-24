// Canonical cubical path operations and their groupoid laws. These builders
// emit ordinary checked syntax; no strict computation law for J is assumed.
import {T,fill} from './core.mjs';
import {interval as I,face as F} from './lattice.mjs';
import {withNativeReferences,withFreshSyntaxNames} from './equivalence.mjs';

function build(inputs,body,budget={}) {
  return withNativeReferences(inputs,(...terms)=>
    withFreshSyntaxNames(terms,fresh=>body(fresh,...terms),budget),budget);
}
const at=(p,i)=>T.at(p,I.variable(i));
const wall=(i,n,term)=>({face:F.endpoint(i,n),term});
const refl=(i,A,x)=>T.line(i,A,x);

export function pathRefl(A,x) {
  return build([A,x],(fresh,A,x)=>refl(fresh('refl'),A,x));
}
export function pathInverse(A,p) {
  return build([A,p],(fresh,A,p)=>{
    const i=fresh('inverse');
    return T.line(i,A,T.at(p,I.reverse(I.variable(i))));
  });
}
export function pathApply(B,f,p) {
  return build([B,f,p],(fresh,B,f,p)=>{
    const i=fresh('apply');
    return T.line(i,B,T.app(f,at(p,i)));
  });
}
export function pathConcat(A,x,p,q,budget={}) {
  return build([A,x,p,q],(fresh,A,x,p,q)=>{
    const i=fresh('path'),j=fresh('compose');
    return T.line(i,A,T.comp(j,A,[wall(i,0,x),wall(i,1,at(q,j))],at(p,i)));
  },budget);
}

// Constant transport need not reduce judgmentally when A is a neutral type.
export function transportConstant(A,x) {
  return build([A,x],(fresh,A,x)=>{
    const i=fresh('law'),j=fresh('transport');
    return T.line(i,A,T.comp(j,A,[wall(i,1,x)],x));
  });
}
export function pathRightUnit(A,x,y,p) {
  return build([A,x,y,p],(fresh,A,x,y,p)=>{
    const i=fresh('path'),j=fresh('compose'),k=fresh('law');
    return T.line(k,T.path(i,A,x,y),T.line(i,A,T.comp(j,A,[
      wall(i,0,x),wall(i,1,y),wall(k,1,at(p,i)),
    ],at(p,i))));
  });
}
export function pathLeftUnit(A,x,y,p) {
  return build([A,x,y,p],(fresh,A,x,y,p)=>{
    const i=fresh('path'),j=fresh('compose'),k=fresh('law');
    const square=T.at(p,I.meet(I.variable(i),I.variable(j)));
    return T.line(k,T.path(i,A,x,y),T.line(i,A,T.comp(j,A,[
      wall(i,0,x),wall(i,1,at(p,j)),wall(k,1,square),
    ],x)));
  });
}
export function pathInverseRight(A,x,y,p) {
  return build([A,x,y,p],(fresh,A,x,y,p)=>{
    const i=fresh('path'),j=fresh('compose'),k=fresh('law');
    const backwards=I.reverse(I.variable(j));
    const square=T.at(p,I.meet(I.variable(i),backwards));
    return T.line(k,T.path(i,A,x,x),T.line(i,A,T.comp(j,A,[
      wall(i,0,x),wall(i,1,T.at(p,backwards)),wall(k,1,square),
    ],at(p,i))));
  });
}
export function pathInverseLeft(A,x,y,p) {
  return build([A,x,y,p],(fresh,A,x,y,p)=>{
    const i=fresh('path'),j=fresh('compose'),k=fresh('law');
    const backwards=I.reverse(I.variable(i));
    const square=T.at(p,I.join(backwards,I.variable(j)));
    return T.line(k,T.path(i,A,y,y),T.line(i,A,T.comp(j,A,[
      wall(i,0,y),wall(i,1,at(p,j)),wall(k,1,square),
    ],T.at(p,backwards))));
  });
}
export function pathAssociative(A,x,y,z,w,p,q,r) {
  return build([A,x,y,z,w,p,q,r],(fresh,A,x,y,z,w,p,q,r)=>{
    const i=fresh('path'),j=fresh('inner'),k=fresh('outer'),s=fresh('law');
    // L fills p followed by q; Q fills q followed by r.
    const L=fill(j,A,[wall(i,0,x),wall(i,1,at(q,j))],at(p,i),I.variable(j));
    const Q=fill(k,A,[wall(j,0,y),wall(j,1,at(r,k))],at(q,j),I.variable(k));
    const pq=T.comp(j,A,[wall(i,0,x),wall(i,1,at(q,j))],at(p,i));
    // H has base pq, endpoint walls x and r, and top p followed by qr.
    const H=T.comp(j,A,[wall(i,0,x),wall(i,1,Q),wall(k,0,L)],at(p,i));
    return T.line(s,T.path(i,A,x,w),T.line(i,A,T.comp(k,A,[
      wall(i,0,x),wall(i,1,at(r,k)),wall(s,1,H),
    ],pq)));
  });
}

// Applying f to the filling of p·q gives a second filling of the square
// defining ap(f,p)·ap(f,q). A comparison cube relates their top edges.
export function pathApplyConcat(A,B,f,x,y,z,p,q) {
  return build([A,B,f,x,y,z,p,q],(fresh,A,B,f,x,y,z,p,q)=>{
    const i=fresh('path'),j=fresh('compose'),k=fresh('naturality');
    const square=fill(j,A,[wall(i,0,x),wall(i,1,at(q,j))],at(p,i),I.variable(j));
    const family=T.path(i,B,T.app(f,x),T.app(f,z));
    return T.line(k,family,T.line(i,B,T.comp(j,B,[
      wall(i,0,T.app(f,x)),wall(i,1,T.app(f,at(q,j))),wall(k,0,T.app(f,square)),
    ],T.app(f,at(p,i)))));
  });
}
