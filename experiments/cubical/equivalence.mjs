// Derived CCHM equivalence operations. These functions only BUILD inert terms;
// the ordinary reference/native checker must verify every result. The fiber
// orientation is y = f(x), matching CCHM §5.3 (the reverse of some HoTT APIs).
import {T} from './core.mjs';
import {interval as I} from './lattice.mjs';
const v=T.variable,ap=T.app,fst=T.first,snd=T.second;

// Reserve even bound spellings, making these syntax builders hygienic without
// depending on the checker's later alpha-renaming. Dimensions are reserved too.
function fresh(base,...terms) {
  const used=new Set();
  const visit=x=>{
    if(typeof x==='string')used.add(x.replace(/:[01]$/,''));
    else if(x&&typeof x==='object')for(const value of Object.values(x))visit(value);
  };
  terms.forEach(visit);
  while(used.has(base))base+='_';
  return base;
}
const path=(A,a,b)=>T.path(fresh('fiber_path',A,a,b),A,a,b);
export function contractible(A) {
  const c=fresh('center',A),x=fresh('point',A,c);
  return T.sigma(c,A,T.pi(x,A,path(A,v(c),v(x))));
}
export function fiber(A,B,f,y) {
  const x=fresh('preimage',A,B,f,y);
  return T.sigma(x,A,path(B,y,ap(f,v(x))));
}
export function equiv(A,B) {
  const f=fresh('function',A,B),x=fresh('argument',A,B,f),y=fresh('target',A,B,f,x);
  return T.sigma(f,T.pi(x,A,B),T.pi(y,B,contractible(fiber(A,B,v(f),v(y)))));
}

// The singleton (x:B) × Path B y x contracts by moving along its path.
// Both endpoint equations check by interval reduction and Sigma/Path eta.
export function identityEquivalence(B) {
  const x=fresh('argument',B),y=fresh('target',B,x),u=fresh('point',B,x,y);
  const i=fresh('i',B,x,y,u),j=fresh('j',B,x,y,u,i);
  const id=T.lam(x,B,v(x)),F=fiber(B,B,id,v(y));
  const center=T.pair(F,v(y),T.line(j,B,v(y)));
  const along=T.at(snd(v(u)),I.variable(i));
  const segment=T.line(j,B,T.at(snd(v(u)),I.meet(I.variable(i),I.variable(j))));
  const contraction=T.lam(u,F,T.line(i,F,T.pair(F,along,segment)));
  const proof=T.lam(y,B,T.pair(contractible(F),center,contraction));
  return T.pair(equiv(B,B),id,proof);
}

// Extend a compatible partial element of a contractible type. This is a
// composition in A, with walls following the center-to-point contraction.
export function extendContractible(A,proof,system) {
  const i=fresh('extension',A,proof,system);
  return T.comp(i,A,system.map(({face,term})=>({face,
    term:T.at(ap(snd(proof),term),I.variable(i))})),fst(proof));
}
