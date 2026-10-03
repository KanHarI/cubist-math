import "../../../tests/fresh-build.mjs";
import test from 'node:test';
import assert from 'node:assert/strict';
import {T} from '../core.mjs';
import {identityEquivalence} from '../equivalence.mjs';
import {face as F,interval as I} from '../lattice.mjs';
import {checkKernel} from './kernel-check.mjs';
const ref=name=>({tag:'Ref',name});
const v=T.variable;
// Two points, the examples' small inductive type.
const two=T.sum(T.unit,T.unit),left=T.inl(two,T.point),right=T.inr(two,T.point);

test('checked definitions stay named, unfold on demand and reject bad declarations',()=>{
  const definitions=[{name:'N',value:two},{name:'one',value:right,type:ref('N')},
    {name:'identity',value:T.lam('x',ref('N'),v('x'))}];
  const folded=checkKernel(ref('one'),ref('N'),[],{definitions,normalize:false});
  assert(folded.ok,folded.error);
  assert.deepEqual(folded.term,ref('one'));
  const applied=checkKernel(T.app(ref('identity'),ref('one')),two,[],{definitions});
  assert(applied.ok,applied.error);
  assert.deepEqual(applied.normal,right);
  assert.equal(checkKernel(left,null,[],{definitions:[{name:'wrong',value:left,type:T.unit}]}).ok,false);
  assert.equal(checkKernel(left,null,[],{definitions:[{name:'open',value:v('x')}]}).ok,false);
  // A name defined again with the same judgement is the same fact; with another body it is refused.
  assert.equal(checkKernel(left,null,[],{definitions:[{name:'n',value:left},{name:'n',value:left}]}).ok,true);
  assert.match(checkKernel(left,null,[],{definitions:[{name:'n',value:left},{name:'n',value:right}]}).error,/already registered/);
});

test('transport along a defined univalence path unfolds its definitions',()=>{
  const identity=identityEquivalence(two);
  const path=T.line('u',T.universe(0),T.glueType(two,[
    {face:F.endpoint('u',0),type:two,equiv:ref('identity')},
    {face:F.endpoint('u',1),type:two,equiv:ref('identity')},
  ]));
  const moved=T.comp('j',T.at(ref('ua'),I.variable('j')),[],right);
  const definitions=[{name:'identity',value:identity},{name:'ua',value:path}];
  const result=checkKernel(moved,two,[],{definitions});
  assert(result.ok,result.error);
  assert.deepEqual(result.normal,right);
});

test('definition references compare distinct bodies rather than assuming all constants equal',()=>{
  const definitions=[{name:'zero',value:left},{name:'one',value:right}];
  const proof=T.line('i',two,ref('zero'));
  const falseType=T.path('i',two,ref('one'),ref('one'));
  assert.equal(checkKernel(proof,falseType,[],{definitions,normalize:false}).ok,false);
});
