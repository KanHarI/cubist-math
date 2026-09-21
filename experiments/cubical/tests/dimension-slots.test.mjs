import test from 'node:test';
import assert from 'node:assert/strict';
import {T} from '../core.mjs';
import {interval as I,face as F} from '../lattice.mjs';
import {bindDimensions,freeDimensions} from '../dimension-slots.mjs';
import {checkNative,nativeRequest} from '../native.mjs';
const v=T.variable;

test('unused ancestor names do not consume interval slots',()=>{
  const dimensions=new Map(Array.from({length:64},(_,i)=>[`outer${i}`,i]));
  const result=bindDimensions(T.path('inner',T.nat,T.zero,T.zero),dimensions);
  assert.equal(result.dim,0);
  assert.deepEqual([...result.inner],[['inner',0]]);
});
test('bound and outer positions have different dimension scopes',()=>{
  const at=name=>T.at(v('p'),I.variable(name));
  const dim=new Map([['outer',0],['other',1]]);
  const path=T.path('inner',at('outer'),at('other'),at('other'));
  assert.equal(bindDimensions(path,dim).dim,1);
  assert.deepEqual([...freeDimensions(path)].sort(),['other','outer']);
  const comp=T.comp('inner',T.nat,[{face:F.endpoint('other',0),term:at('outer')}],at('other'));
  assert.equal(bindDimensions(comp,dim).dim,1);
  assert.deepEqual([...freeDimensions(comp)].sort(),['other','outer']);
  const hcomp=T.hcomp('inner',at('outer'),[{face:F.endpoint('other',0),term:T.zero}],T.zero);
  assert.equal(bindDimensions(hcomp,dim).dim,0);
  assert.deepEqual([...freeDimensions(hcomp)].sort(),['other','outer']);
  const trans=T.trans('inner',at('outer'),F.endpoint('other',0),at('other'));
  assert.equal(bindDimensions(trans,dim).dim,1);
});
test('simultaneously used outer coordinates remain distinct and the real limit is enforced',()=>{
  const dimensions=new Map(Array.from({length:64},(_,i)=>[`d${i}`,i]));
  const arg=[Array.from({length:64},(_,i)=>`d${i}:1`)];
  const line=T.line('new',T.nat,T.at(v('p'),arg));
  assert.throws(()=>bindDimensions(line,dimensions),/simultaneously live/);
  const pair=T.pair(T.sigma('n',T.nat,T.nat),T.at(v('p'),I.variable('d0')),T.at(v('p'),I.variable('d1')));
  const scope=bindDimensions(T.line('new',T.sigma('n',T.nat,T.nat),pair),dimensions);
  assert.equal(scope.dim,2);
  assert.deepEqual([...scope.inner],[['d0',0],['d1',1],['new',2]]);
});
test('100 nested constant path binders check natively using live slots',()=>{
  // Register successive closed levels: an unfolded tree would duplicate each
  // previous type and endpoint exponentially, unrelated to dimension liveness.
  const definitions=[];
  let type=T.nat,value=T.zero;
  for(let i=0;i<100;i++) {
    const name=`level${i}`;
    definitions.push({name,value:T.line(`path${i}`,type,value)});
    value={tag:'Ref',name};
    type=T.path(`path${i}`,type,i?{tag:'Ref',name:`level${i-1}`}:T.zero,i?{tag:'Ref',name:`level${i-1}`}:T.zero);
  }
  const result=checkNative(value,type,[],{definitions,normalize:false});
  assert(result.ok,result.error);
});
test('dimension liveness memoizes immutable shared syntax and rejects free coordinates',()=>{
  const p=T.path('i',T.nat,T.zero,T.zero);
  const bad=T.line('i',T.nat,T.at(v('p'),I.variable('missing')));
  assert.throws(()=>nativeRequest(bad,null,[['p',p]]),/Unbound serialized dimension/);
  let shared=T.nat;
  for(let i=0;i<28;i++)shared=T.sigma(`x${i}`,shared,shared);
  assert.deepEqual([...freeDimensions(shared)],[]);
  assert(Object.isFrozen(shared));
});
