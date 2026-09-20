import test from 'node:test';
import assert from 'node:assert/strict';
import {Checker,T} from '../core.mjs';
import {identityEquivalence} from '../equivalence.mjs';
import {face as F,interval as I} from '../lattice.mjs';
import {checkNative} from '../native.mjs';
const ref=name=>({tag:'Ref',name});
const v=T.variable;

test('checked native definitions stay named, unfold on demand and reject bad declarations',()=>{
  const definitions=[{name:'N',value:T.nat},{name:'one',value:T.succ(T.zero),type:ref('N')},
    {name:'identity',value:T.lam('x',ref('N'),v('x'))}];
  const folded=checkNative(ref('one'),ref('N'),[],{definitions,normalize:false});
  assert(folded.ok,folded.error);
  assert.deepEqual(folded.normal,ref('one'));
  const applied=checkNative(T.app(ref('identity'),ref('one')),T.nat,[],{definitions});
  assert(applied.ok,applied.error);
  assert.deepEqual(applied.normal,T.succ(T.zero));
  assert.equal(checkNative(T.zero,null,[],{definitions:[{name:'wrong',value:T.zero,type:T.unit}]}).ok,false);
  assert.equal(checkNative(T.zero,null,[],{definitions:[{name:'open',value:v('x')}]}).ok,false);
  assert.equal(checkNative(T.zero,null,[],{definitions:[{name:'n',value:T.zero},{name:'n',value:T.zero}]}).ok,false);
});

test('definition checks preserve protocol aliases across internal formula and node allocations',()=>{
  const identity=identityEquivalence(T.nat);
  const path=T.line('u',T.universe(0),T.glueType(T.nat,[
    {face:F.endpoint('u',0),type:T.nat,equiv:ref('identity')},
    {face:F.endpoint('u',1),type:T.nat,equiv:ref('identity')},
  ]));
  const moved=T.comp('j',T.at(ref('ua'),I.variable('j')),[],T.succ(T.zero));
  const definitions=[{name:'identity',value:identity},{name:'ua',value:path}];
  const result=checkNative(moved,T.nat,[],{definitions});
  assert(result.ok,result.error);
  assert.deepEqual(result.normal,T.succ(T.zero));
  new Checker().verify(result.normal,T.nat);
});

test('native definition references compare distinct bodies rather than assuming all constants equal',()=>{
  const definitions=[{name:'zero',value:T.zero},{name:'one',value:T.succ(T.zero)}];
  const proof=T.line('i',T.nat,ref('zero'));
  const falseType=T.path('i',T.nat,ref('one'),ref('one'));
  assert.equal(checkNative(proof,falseType,[],{definitions,normalize:false}).ok,false);
});
