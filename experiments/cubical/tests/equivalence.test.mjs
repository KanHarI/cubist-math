import test from 'node:test';
import assert from 'node:assert/strict';
import {Checker,T} from '../core.mjs';
import {equiv,identityEquivalence,contractible,extendContractible} from '../equivalence.mjs';
import {face as F,interval as I} from '../lattice.mjs';
import {checkNative} from '../native.mjs';
function check(term,type,ctx=[]) {
  const js=new Checker(),expected=js.verify(term,type,ctx),native=checkNative(term,type,ctx);
  assert(native.ok,native.error);
  assert(js.equal(native.type,expected.type));
  assert(js.equal(native.normal,expected.normal));
}
test('identity equivalence is constructed from contractible fibers in both checkers',()=>{
  check(identityEquivalence(T.nat),equiv(T.nat,T.nat));
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
