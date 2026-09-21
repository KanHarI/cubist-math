// Dependent transport laws for the canonical cubical operations. These are
// derived terms; the trusted checking and computation rules remain unchanged.
import {T,fill} from './core.mjs';
import {interval as I,face as F} from './lattice.mjs';
import {withNativeReferences} from './equivalence.mjs';
import {dependentPathToTransport} from './path-over.mjs';
import {pathRefl,pathInverse,pathApply,pathConcat,
  pathLeftUnit,pathRightUnit,pathInverseLeft,pathInverseRight,pathAssociative} from './path-algebra.mjs';
const v=T.variable,app=T.app;
const at=(p,i)=>T.at(p,I.variable(i));
const wall=(i,n,term)=>({face:F.endpoint(i,n),term});
const eq=(i,A,x,y)=>T.path(i,A,x,y);
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
export function pathTransport(C,p,value) {
  return build([C,p,value],(fresh,C,p,value)=>{
    const i=fresh('transport');
    return T.comp(i,app(C,at(p,i)),[],value);
  });
}
export function transportInverseAfter(A,C,x,y,p,value) {
  return build([A,C,x,y,p,value],(fresh,A,C,x,y,p,value)=>{
    const i=fresh('along'),j=fresh('backwards'),k=fresh('law');
    const backwards=I.reverse(I.variable(j));
    const family=app(C,at(p,i));
    const filledBackwards=fill(i,family,[],value,backwards);
    const transported=T.comp(i,family,[],value);
    return T.line(k,app(C,x),T.comp(j,app(C,T.at(p,backwards)),[
      wall(k,1,filledBackwards),
    ],transported));
  });
}
export function transportAfterInverse(A,C,x,y,p,value) {
  return transportInverseAfter(A,C,y,x,pathInverse(A,p),value);
}
export function transportConcat(A,C,x,y,z,p,q,value) {
  return build([A,C,x,y,z,p,q,value],(fresh,A,C,x,y,z,p,q,value)=>{
    const i=fresh('path'),j=fresh('compose');
    const pq=pathConcat(A,x,p,q);
    const first=pathTransport(C,p,value);
    const last=pathTransport(C,q,first);
    const base=fill(i,app(C,at(p,i)),[],value,I.variable(i));
    const right=fill(j,app(C,at(q,j)),[],first,I.variable(j));
    // Fill the concatenation square in A, then fill the lifted square in C.
    const square=fill(j,A,[wall(i,0,x),wall(i,1,at(q,j))],at(p,i),I.variable(j));
    const family=app(C,at(pq,i));
    const lifted=T.line(i,family,T.comp(j,app(C,square),[
      wall(i,0,value),wall(i,1,right),
    ],base));
    return app(dependentPathToTransport(i,family,value,last),lifted);
  });
}
// With direct ap, the two families coincide by beta computation.
export function transportApply(C,p,value) {
  return pathRefl(app(C,T.at(p,I.one)),pathTransport(C,p,value));
}
export function transportDecoder(A,origin,C,x,y,p,f,value) {
  return build([A,origin,C,x,y,p,f,value],(fresh,A,origin,C,x,y,p,f,value)=>{
    const point=fresh('point'),arg=fresh('argument'),i=fresh('path');
    const family=T.lam(point,A,T.pi(arg,app(C,v(point)),eq(i,A,origin,v(point))));
    const result=app(pathTransport(family,p,f),value);
    // Pi composition transports the argument backwards. Path composition
    // then appends p, precisely the desired decoder formula.
    return pathRefl(eq(i,A,origin,y),result);
  });
}
export function dependentApply(C,f,x,y,p) {
  return build([C,f,x,y,p],(fresh,C,f,x,y,p)=>{
    const i=fresh('path'),family=app(C,at(p,i));
    const action=T.line(i,family,app(f,at(p,i)));
    return app(dependentPathToTransport(i,family,app(f,x),app(f,y)),action);
  });
}
export function dependentApplyConstant(A,B,f,x,y,p) {
  return build([A,B,f,x,y,p],(fresh,A,B,f,x,y,p)=>{
    const i=fresh('compose'),j=fresh('path'),k=fresh('law');
    const a=app(f,x),b=app(f,y),r=pathApply(B,f,p);
    const transported=T.comp(i,B,[],a);
    // L(j,k) fills constant transport with the j=1 edge held at a.
    const L=fill(i,B,[wall(j,1,a)],a,I.variable(k));
    const F=fill(i,B,[],a,I.join(I.variable(i),I.variable(k)));
    return T.line(k,eq(j,B,transported,b),T.line(j,B,T.comp(i,B,[
      wall(j,0,F),wall(j,1,at(r,i)),
    ],L)));
  });
}
export function cancelLeft(A,x,y,z,p,q,r,same) {
  return build([A,x,y,z,p,q,r,same],(fresh,A,x,y,z,p,q,r,same)=>{
    const i=fresh('path'),s=fresh('loop'),t=fresh('following');
    const inverse=pathInverse(A,p),Y=eq(i,A,y,z);
    const cancel=following=>{
      const intermediate=pathConcat(A,y,pathConcat(A,y,inverse,p),following);
      const assoc=pathAssociative(A,y,x,y,z,inverse,p,following);
      const replace=T.lam(s,eq(i,A,y,y),pathConcat(A,y,v(s),following));
      const simplify=pathApply(Y,replace,pathInverseLeft(A,x,y,p));
      return pathConcat(Y,pathConcat(A,y,inverse,pathConcat(A,x,p,following)),
        pathInverse(Y,assoc),pathConcat(Y,intermediate,simplify,pathLeftUnit(A,y,z,following)));
    };
    const cq=cancel(q),cr=cancel(r);
    const prefix=T.lam(t,eq(i,A,x,z),pathConcat(A,y,inverse,v(t)));
    const middle=pathApply(Y,prefix,same);
    return pathConcat(Y,q,pathInverse(Y,cq),pathConcat(Y,
      pathConcat(A,y,inverse,pathConcat(A,x,p,q)),middle,cr));
  });
}

export function appendCancelInverse(A,x,y,z,p,q) {
  return build([A,x,y,z,p,q],(fresh,A,x,y,z,p,q)=>{
    const i=fresh('path'),loop=fresh('loop');
    const resultType=eq(i,A,x,y),inverse=pathInverse(A,q);
    const initial=pathConcat(A,x,pathConcat(A,x,p,q),inverse);
    const associated=pathConcat(A,x,p,pathConcat(A,y,q,inverse));
    const assoc=pathAssociative(A,x,y,z,y,p,q,inverse);
    const prefix=T.lam(loop,eq(i,A,y,y),pathConcat(A,x,p,v(loop)));
    const simplify=pathApply(resultType,prefix,pathInverseRight(A,y,z,q));
    const last=pathRightUnit(A,x,y,p);
    return pathConcat(resultType,initial,assoc,
      pathConcat(resultType,associated,simplify,last));
  });
}
export function appendInverseCancel(A,x,y,z,p,q) {
  return appendCancelInverse(A,x,y,z,p,pathInverse(A,q));
}
