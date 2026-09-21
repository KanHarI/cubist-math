// Direct path-algebra helpers used by the existing adjointification proof.
// They preserve its supplied forward map, inverse and section homotopy.
import {T} from './core.mjs';
import {interval as I,face as F} from './lattice.mjs';
import {withNativeReferences} from './equivalence.mjs';
import {pathRefl,pathInverse,pathApply,pathConcat,pathAssociative,
  pathInverseLeft,pathLeftUnit} from './path-algebra.mjs';
import {appendCancelInverse} from './dependent-transport.mjs';
const v=T.variable,app=T.app;
const at=(p,i)=>T.at(p,I.variable(i));
const eq=(A,x,y)=>build([A,x,y],(fresh,A,x,y)=>T.path(fresh('equality'),A,x,y));
function build(inputs,body) {
  return withNativeReferences(inputs,(...terms)=>{
    const used=new Set();
    const reserve=value=>{
      if(typeof value==='string')used.add(value.replace(/:[01]$/,''));
      else if(value&&typeof value==='object')Object.values(value).forEach(reserve);
    };
    terms.forEach(reserve);
    const fresh=stem=>{while(used.has(stem))stem+='_';used.add(stem);return stem;};
    return body(fresh,...terms);
  });
}
export function cancelRight(A,x,y,z,p,q,r,same) {
  return build([A,x,y,z,p,q,r,same],(fresh,A,x,y,z,p,q,r,same)=>{
    const name=fresh('prefix'),P=eq(A,x,y),inverse=pathInverse(A,r);
    const append=T.lam(name,eq(A,x,z),pathConcat(A,x,v(name),inverse));
    const first=pathInverse(P,appendCancelInverse(A,x,y,z,p,r));
    const middle=pathApply(P,append,same);
    const last=appendCancelInverse(A,x,y,z,q,r);
    return pathConcat(P,p,first,pathConcat(P,
      pathConcat(A,x,pathConcat(A,x,p,r),inverse),middle,last));
  });
}
export function prependInverseCancel(A,x,y,z,p,q) {
  return build([A,x,y,z,p,q],(fresh,A,x,y,z,p,q)=>{
    const name=fresh('loop'),P=eq(A,y,z),inverse=pathInverse(A,p);
    const initial=pathConcat(A,y,inverse,pathConcat(A,x,p,q));
    const assoc=pathInverse(P,pathAssociative(A,y,x,y,z,inverse,p,q));
    const append=T.lam(name,eq(A,y,y),pathConcat(A,y,v(name),q));
    const middle=pathApply(P,append,pathInverseLeft(A,x,y,p));
    return pathConcat(P,initial,assoc,pathConcat(P,
      pathConcat(A,y,pathConcat(A,y,inverse,p),q),middle,pathLeftUnit(A,y,z,q)));
  });
}
export function homotopyNatural(A,f,h,x,y,p) {
  return build([A,f,h,x,y,p],(fresh,A,f,h,x,y,p)=>{
    const i=fresh('path'),j=fresh('compose'),k=fresh('triangle');
    const H=(r,s)=>T.at(app(h,T.at(p,r)),s);
    const fx=app(f,x),P=eq(A,fx,y);
    const left=pathConcat(A,fx,pathApply(A,f,p),app(h,y));
    const first=T.line(k,P,T.line(i,A,T.comp(j,A,[
      {face:F.endpoint(i,0),term:fx},
      {face:F.endpoint(i,1),term:at(app(h,y),j)},
      {face:F.endpoint(k,1),term:H(I.variable(i),I.meet(I.variable(i),I.variable(j)))},
    ],app(f,at(p,i)))));
    const second=T.line(k,P,T.line(i,A,T.comp(j,A,[
      {face:F.endpoint(i,0),term:fx},
      {face:F.endpoint(i,1),term:at(p,j)},
      {face:F.endpoint(k,1),term:H(I.meet(I.variable(i),I.variable(j)),I.variable(i))},
    ],at(app(h,x),i))));
    return pathConcat(P,left,first,pathInverse(P,second));
  });
}
export function homotopySelf(A,f,h,x) {
  const fx=app(f,x),ffx=app(f,fx),p=pathApply(A,f,app(h,x)),q=app(h,fx),r=app(h,x);
  return cancelRight(A,ffx,fx,x,p,q,r,homotopyNatural(A,f,h,fx,x,r));
}
export function applyInterchange(A,B,f,g,x,y,p) {
  return build([A,B,f,g,x,y,p],(fresh,A,B,f,g,x,y,p)=>{
    const a=fresh('argument');
    const gf=T.lam(a,A,app(g,app(f,v(a))));
    const lhs=pathApply(B,f,pathApply(A,gf,p));
    return pathRefl(eq(B,app(f,app(g,app(f,x))),app(f,app(g,app(f,y)))),lhs);
  });
}
