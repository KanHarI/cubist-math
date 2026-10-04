import "../fresh-build.mjs";
import test from 'node:test';
import assert from 'node:assert/strict';
import {T,withoutEmptyFaces} from '../../web/translator/core.mjs';
import {face as F,interval as I} from '../../web/translator/lattice.mjs';
import {checkKernel} from './kernel-check.mjs';
import {equiv,identityEquivalence,strictIsomorphismEquivalence} from '../../web/translator/equivalence.mjs';
import {unglueEquivalence} from './unglue-equivalence-fixture.mjs';
// Two points, the examples' small inductive type.
const two=T.sum(T.unit,T.unit),left=T.inl(two,T.point),right=T.inr(two,T.point);
const v=T.variable;
function checked(term,type,context=[]) {
  const native=checkKernel(term,type,context,{normalize:false});
  assert(native.ok,native.error);
  return native;
}

// The unglue equivalence, the contractibility of the type of types
// equivalent to a type, and univalence itself are proved in Cubist, in
// library/univalence.cubist.

// The fixture's unglue equivalence along a line of Glue types checks, and so
// does its normal form, at the type the kernel inferred (without its parts
// on the face 0, as a definition's type is). There two tubes' agreement is a
// composition whose tube the kernel's reduction leaves on a face of two
// clauses, i = 0 ∨ j = 0, where the other side has a tube on each: the
// driver splits it by the kernel's split step (work plan I1.2c).
test('unglue is a derived equivalence, and its normal form checks again',()=>{
  const A=v('A'),X=v('X'),e=v('e');
  const context=[['A',T.universe(0)],['X',T.universe(0)],['e',equiv(X,A)]];
  const G=T.glueType(A,[{face:F.endpoint('i',0),type:X,equiv:e}]);
  const result=checkKernel(T.line('i',equiv(G,A),unglueEquivalence(G)),null,context);
  assert(result.ok,result.error);
  checked(result.normal,withoutEmptyFaces(result.type),context);
});
test('actual univalence transport computes a nonidentity product-swap equivalence',()=>{
  const A=T.sigma('n',two,T.unit),B=T.sigma('u',T.unit,two);
  const forward=T.lam('p',A,T.pair(B,T.second(v('p')),T.first(v('p'))));
  const inverse=T.lam('q',B,T.pair(A,T.second(v('q')),T.first(v('q'))));
  const e=strictIsomorphismEquivalence(A,B,forward,inverse);
  checked(e,equiv(A,B));
  const ua=T.line('i',T.universe(0),T.glueType(B,[
    {face:F.endpoint('i',0),type:A,equiv:e},
    {face:F.endpoint('i',1),type:B,equiv:identityEquivalence(B)},
  ]));
  const input=T.pair(A,right,T.point);
  const moved=T.comp('j',T.at(ua,I.variable('j')),[],input);
  const native=checkKernel(moved,B);
  assert(native.ok,native.error);
  assert.deepEqual(native.normal.first,T.point);
  assert.deepEqual(native.normal.second,right);
  assert(checkKernel(native.normal,B,[],{normalize:false}).ok);
  const notInverse=T.lam('q',B,T.pair(A,left,T.point));
  assert.equal(checkKernel(strictIsomorphismEquivalence(A,B,forward,notInverse),equiv(A,B),[],{normalize:false}).ok,false);
});
