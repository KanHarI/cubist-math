import "../fresh-build.mjs";
import test from 'node:test';
import assert from 'node:assert/strict';
import {T} from '../../web/translator/core.mjs';
import {face as F,interval as I} from '../../web/translator/lattice.mjs';
import {checkKernel} from './kernel-check.mjs';
import {equiv,identityEquivalence,strictIsomorphismEquivalence} from '../../web/translator/equivalence.mjs';
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
