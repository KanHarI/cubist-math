import test from 'node:test';
import assert from 'node:assert/strict';
import {Checker,T} from '../core.mjs';
import {face as F,interval as I} from '../lattice.mjs';
import {checkNative} from '../native.mjs';
const v=T.variable;
function checked(term,type=null,context=[]) {
  const reference=new Checker({fuel:1000000});
  const expected=reference.verify(term,type,context);
  const result=checkNative(term,type,context);
  assert(result.ok,result.error);
  assert(reference.equal(result.normal,expected.normal));
  reference.verify(result.normal,expected.type,context);
  const nativeRecheck=checkNative(result.normal,expected.type,context,{normalize:false});
  assert(nativeRecheck.ok,nativeRecheck.error);
  return result.normal;
}

test('native sum composition preserves constructors and computes their payloads',()=>{
  const sum=T.sum(T.nat,T.unit);
  for(const value of [T.inl(sum,T.succ(T.zero)),T.inr(sum,T.point)]) {
    assert.deepEqual(checked(T.comp('i',sum,[],value),sum),value);
    const wall=T.line('j',sum,T.comp('i',sum,[{face:F.endpoint('j',0),term:value}],value));
    checked(wall);
  }
});

test('native W composition composes labels and transports dependent child domains',()=>{
  const W=T.w('label',T.unit,T.void);
  const leaf=T.sup(W,T.point,T.lam('empty',T.void,T.abort(W,v('empty'))));
  const moved=T.comp('i',W,[],leaf);
  const result=checked(moved,W);
  assert.equal(result.tag,'Sup');
  assert.deepEqual(result.label,T.point);
  const motive=T.lam('tree',W,T.nat);
  const step=T.lam('label',T.unit,T.lam('children',T.pi('e',T.void,W),
    T.lam('hypotheses',T.pi('e',T.void,T.nat),T.succ(T.zero))));
  assert.deepEqual(checked(T.wrec(motive,step,moved),T.nat),T.succ(T.zero));
});

test('native W composition respects a nonempty wall and its boundary',()=>{
  const W=T.w('label',T.unit,T.void);
  const leaf=T.sup(W,T.point,T.lam('empty',T.void,T.abort(W,v('empty'))));
  const line=T.line('j',W,T.comp('i',W,[{face:F.endpoint('j',0),term:leaf}],leaf));
  checked(line);
  checked(T.at(line,I.zero),W);
});

test('native W composition checks a varying label type and varying arity family',()=>{
  const U=T.universe(0);
  for(const varyLabels of [true,false]) {
    const endpoints=varyLabels?T.unit:T.void;
    const P=v('P'),context=[['P',T.path('j',U,endpoints,endpoints)]];
    const family=T.w('label',varyLabels?T.at(P,I.variable('i')):T.unit,
      varyLabels?T.void:T.at(P,I.variable('i')));
    const start=T.w('label',T.unit,T.void);
    const leaf=T.sup(start,T.point,T.lam('empty',T.void,T.abort(start,v('empty'))));
    checked(T.comp('i',family,[],leaf),start,context);
  }
});
