import "../fresh-build.mjs";
import test from 'node:test';
import assert from 'node:assert/strict';
import {T} from '../../web/translator/core.mjs';
import {equiv,identityEquivalence,contractible,extendContractible} from '../../web/translator/equivalence.mjs';
import {face as F,interval as I} from '../../web/translator/lattice.mjs';
import {checkKernel} from './kernel-check.mjs';
// Two points, the examples' small inductive type.
const two=T.sum(T.unit,T.unit),left=T.inl(two,T.point),right=T.inr(two,T.point);
// The kernel checks the term, and its normal form checks at the same type.
function check(term,type,ctx=[]) {
  const native=checkKernel(term,type,ctx);
  assert(native.ok,native.error);
  const again=checkKernel(native.normal,native.type,ctx,{normalize:false});
  assert(again.ok,again.error);
}
test('identity equivalence is constructed from contractible fibers',()=>{
  check(identityEquivalence(two),equiv(two,two));
  const A=T.variable('A');
  check(identityEquivalence(A),equiv(A,A),[['A',T.universe(0)]]);
});
test('contractible-fiber extension is derived checked composition',()=>{
  const A=T.variable('A'),c=T.variable('c'),x=T.variable('x');
  const ctx=[['A',T.universe(0)],['c',contractible(A)],['x',A]];
  const extension=T.line('i',A,extendContractible(A,c,[{face:F.endpoint('i',1),term:x}]));
  check(extension,T.path('i',A,T.comp('extension',A,[],T.first(c)),x),ctx);
});
test('universal face quantification is not Boolean endpoint coverage',()=>{
  const endpoints=F.join(F.endpoint('i',0),F.endpoint('i',1));
  assert(F.equal(F.forall('i',endpoints),F.bottom));
  assert(F.equal(F.forall('i',F.join(endpoints,F.endpoint('j',0))),F.endpoint('j',0)));
  assert(F.equal(F.forall('i',F.top),F.top));
});
