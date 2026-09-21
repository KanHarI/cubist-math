// Bridge the public half-adjoint presentation with CCHM contractible fibers.
// These are derived terms, not additional equivalence or univalence axioms.
import {T} from './core.mjs';
import {interval as I,face as F} from './lattice.mjs';
import {equiv,fiber,contractible,equivalenceFromInverse,equivalenceWitnessPath,withNativeReferences,
  univalencePath,univalenceTransportBeta} from './equivalence.mjs';
import {pathRefl,pathInverse,pathApply} from './path-algebra.mjs';
const v=T.variable,app=T.app,fst=T.first,snd=T.second;
const at=(p,i)=>T.at(p,I.variable(i));
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
function data(fresh,A,B,f,g,eta,epsilon) {
  const x=fresh('source'),y=fresh('target'),i=fresh('path');
  const etaType=T.pi(x,A,eq(i,A,app(g,app(f,v(x))),v(x)));
  const epsilonType=T.pi(y,B,eq(i,B,app(f,app(g,v(y))),v(y)));
  const triangle=T.pi(x,A,eq(i,eq(i,B,app(f,app(g,app(f,v(x)))),app(f,v(x))),
    pathApply(B,f,app(eta,v(x))),app(epsilon,app(f,v(x)))));
  return {etaType,epsilonType,triangle};
}
export function halfAdjointType(A,B,f) {
  return build([A,B,f],(fresh,A,B,f)=>{
    const g=fresh('inverse'),eta=fresh('section'),epsilon=fresh('retraction'),y=fresh('target');
    const d=data(fresh,A,B,f,v(g),v(eta),v(epsilon));
    return T.sigma(g,T.pi(y,B,A),T.sigma(eta,d.etaType,T.sigma(epsilon,d.epsilonType,d.triangle)));
  });
}
export function halfAdjointEquiv(A,B) {
  return build([A,B],(fresh,A,B)=>{
    const f=fresh('forward'),x=fresh('source');
    return T.sigma(f,T.pi(x,A,B),halfAdjointType(A,B,v(f)));
  });
}
export function halfAdjointToNative(A,B,e) {
  return build([A,B,e],(fresh,A,B,e)=>{
    const name=fresh('public_equivalence'),input=v(name);
    const f=fst(input),proof=snd(input),g=fst(proof);
    const eta=fst(snd(proof)),epsilon=fst(snd(snd(proof)));
    return app(T.lam(name,halfAdjointEquiv(A,B),equivalenceFromInverse(A,B,f,g,eta,epsilon)),e);
  });
}
export function nativeToHalfAdjoint(A,B,e) {
  return build([A,B,e],(fresh,A,B,e)=>{
    const f=fst(e),x=fresh('source'),y=fresh('target');
    const i=fresh('section'),j=fresh('path'),k=fresh('triangle'),r=fresh('square');
    const center=target=>fst(app(snd(e),target));
    const g=T.lam(y,B,fst(center(v(y))));
    const source=v(x),target=app(f,source),fiberType=fiber(A,B,f,target);
    const endpoint=T.pair(fiberType,source,pathRefl(B,target));
    const contraction=app(snd(app(snd(e),target)),endpoint);
    const eta=T.lam(x,A,T.line(i,A,fst(at(contraction,i))));
    const epsilon=T.lam(y,B,pathInverse(B,snd(center(v(y)))));
    // The second component of the fiber contraction is a square E(j,r).
    // Its bottom/right edges are constant. Fill between its top edge and
    // the reversed left edge, obtaining the half-adjoint triangle.
    const E=T.at(snd(at(contraction,j)),I.variable(r));
    const boundary=snd(center(target));
    const square=T.comp(r,B,[
      {face:F.endpoint(j,0),term:at(boundary,r)},
      {face:F.endpoint(j,1),term:target},
      {face:F.endpoint(k,0),term:E},
      {face:F.endpoint(k,1),term:T.at(boundary,I.meet(I.variable(r),I.reverse(I.variable(j))))},
    ],target);
    const pathType=eq(j,B,app(f,app(g,target)),target);
    const triangle=T.lam(x,A,T.line(k,pathType,T.line(j,B,square)));
    const en=fresh('section_proof'),ep=fresh('retraction_proof');
    const d=data(fresh,A,B,f,g,v(en),v(ep));
    const epType=T.sigma(ep,d.epsilonType,data(fresh,A,B,f,g,eta,v(ep)).triangle);
    const etaType=T.sigma(en,d.etaType,T.sigma(ep,d.epsilonType,d.triangle));
    const witness=T.pair(halfAdjointType(A,B,f),g,
      T.pair(etaType,eta,T.pair(epType,epsilon,triangle)));
    return T.pair(halfAdjointEquiv(A,B),f,witness);
  });
}
export function publicUnivalencePath(A,B,e,level=0) {
  return univalencePath(A,B,halfAdjointToNative(A,B,e),level);
}
export function publicUnivalenceBeta(A,B,e,x) {
  return build([A,B,e,x],(fresh,A,B,e,x)=>{
    const native=fresh('native_equivalence');
    return app(T.lam(native,equiv(A,B),univalenceTransportBeta(A,B,v(native),x)),
      halfAdjointToNative(A,B,e));
  });
}

// The forward map is preserved definitionally. Native equivalence witnesses
// for that fixed map are propositions, giving this round-trip law.
export function nativeEquivalenceRoundTrip(A,B,e) {
  return build([A,B,e],(fresh,A,B,e)=>{
    const name=fresh('fiber_witness'),y=fresh('target'),f=fst(e);
    const witnessType=T.pi(y,B,contractible(fiber(A,B,f,v(y))));
    const converted=halfAdjointToNative(A,B,nativeToHalfAdjoint(A,B,e));
    const term=equivalenceWitnessPath(A,B,T.pair(equiv(A,B),f,v(name)),e);
    return app(T.lam(name,witnessType,term),snd(converted));
  });
}
