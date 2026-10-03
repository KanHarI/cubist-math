import "../fresh-build.mjs";
import test from 'node:test';
import assert from 'node:assert/strict';
import {T} from '../../web/translator/core.mjs';
import {face as F} from '../../web/translator/lattice.mjs';
import {checkKernel} from './kernel-check.mjs';
// The kernel checks the term, and its normal form checks at the same type.
function checked(term,type=null,context=[]) {
  const result=checkKernel(term,type,context);
  assert(result.ok,result.error);
  const recheck=checkKernel(result.normal,result.type,context,{normalize:false});
  assert(recheck.ok,recheck.error);
  return result.normal;
}

test('sum composition preserves constructors and computes their payloads',()=>{
  const two=T.sum(T.unit,T.unit),sum=T.sum(two,T.unit);
  for(const value of [T.inl(sum,T.inr(two,T.point)),T.inr(sum,T.point)]) {
    assert.deepEqual(checked(T.comp('i',sum,[],value),sum),value);
    const wall=T.line('j',sum,T.comp('i',sum,[{face:F.endpoint('j',0),term:value}],value));
    checked(wall);
  }
});
