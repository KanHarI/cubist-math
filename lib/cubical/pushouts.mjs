// Library constructions over the computational pushout primitive.
import {T} from './core.mjs';
import {interval as I} from './lattice.mjs';
import {withFreshSyntaxNames} from './equivalence.mjs';

export function pushout(C,A,B,f,g,budget={}) {
  return withFreshSyntaxNames([C,A,B,f,g],fresh=>{
    const x=fresh('span_argument'),h=fresh('span_map');
    const maps=T.sigma(h,T.pi(x,C,A),T.pi(x,C,B));
    return T.pushout(C,A,B,T.pair(maps,f,g));
  },budget);
}

export function suspension(A,budget={}) {
  return withFreshSyntaxNames([A],fresh=>{
    const a=fresh('suspension_label'),constant=T.lam(a,A,T.point);
    return pushout(A,T.unit,T.unit,constant,constant,budget);
  },budget);
}
export const north=(A,budget={})=>T.pushLeft(suspension(A,budget),T.point);
export const south=(A,budget={})=>T.pushRight(suspension(A,budget),T.point);
export function meridian(A,a,budget={}) {
  return withFreshSyntaxNames([A,a],fresh=>{
    const i=fresh('meridian'),type=suspension(A,budget);
    return T.line(i,type,T.pushPath(type,a,I.variable(i)));
  },budget);
}
