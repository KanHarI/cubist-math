// Notation for the explicit unary naturals exported by the source library. These are
// generic terms; this module neither declares nor admits a type.
import {T} from "./core.mjs";
export const naturalSort=T.sort("unat__UNat");
export const isNaturalSort=term=>term?.tag==="Sort"&&term.signature==="unat__UNat";
export function numeral(n,type=naturalSort) {
  let term=T.constructor(0,type,"zero"),succ=T.constructor(1,type,"succ");
  for(let i=0;i<n;i++)term=T.app(succ,term);
  return term;
}
export function numeralValue(term) {
  let count=0;
  while(term?.tag==="App"&&term.fn?.tag==="Con"&&term.fn.index===1&&isNaturalSort(term.fn.sort)) {
    count++;term=term.arg;
  }
  return term?.tag==="Con"&&term.index===0&&isNaturalSort(term.sort)?count:null;
}
