// Library constructions over the computational pushout primitive.
import {T} from './core.mjs';
import {interval as I} from './lattice.mjs';

function fresh(stem,...terms) {
  const names=new Set();
  function collect(t) {
    if(typeof t==='string')names.add(t);
    else if(Array.isArray(t))t.forEach(collect);
    else if(t&&typeof t==='object')Object.values(t).forEach(collect);
  }
  terms.forEach(collect);
  while(names.has(stem))stem+='_';
  return stem;
}

export function pushout(C,A,B,f,g) {
  const x=fresh('span_argument',C,A,B,f,g),h=fresh('span_map',C,A,B,f,g);
  const maps=T.sigma(h,T.pi(x,C,A),T.pi(x,C,B));
  return T.pushout(C,A,B,T.pair(maps,f,g));
}

export function suspension(A) {
  const a=fresh('suspension_label',A),constant=T.lam(a,A,T.point);
  return pushout(A,T.unit,T.unit,constant,constant);
}
export const north=A=>T.pushLeft(suspension(A),T.point);
export const south=A=>T.pushRight(suspension(A),T.point);
export function meridian(A,a) {
  const i=fresh('meridian',A,a);
  return T.line(i,suspension(A),T.pushPath(suspension(A),a,I.variable(i)));
}
