import "../../../tests/fresh-build.mjs";
import test from 'node:test';
import assert from 'node:assert/strict';
import {T} from '../core.mjs';
import {face as F,interval as I} from '../lattice.mjs';
import {equiv,equivalenceFromInverse,identityEquivalence} from '../equivalence.mjs';
import {checkKernel} from './kernel-check.mjs';
// Two points, the examples' small inductive type.
const two=T.sum(T.unit,T.unit),left=T.inl(two,T.point),right=T.inr(two,T.point);
const v=T.variable,ap=T.app,path=(A,a,b)=>T.path('i',A,a,b);
function hypotheses(levelA=0,levelB=0) {
  const A=v('A'),B=v('B'),f=v('f'),g=v('g');
  return [['A',T.universe(levelA)],['B',T.universe(levelB)],
    ['f',T.pi('x',A,B)],['g',T.pi('y',B,A)],
    ['eta',T.pi('x',A,path(A,ap(g,ap(f,v('x'))),v('x')))],
    ['epsilon',T.pi('y',B,path(B,ap(f,ap(g,v('y'))),v('y')))]];
}
function close(term,context,kind) {
  for(const [name,type]of [...context].reverse())term=kind(name,type,term);
  return term;
}

test('arbitrary inverse homotopies give a closed checked contractible-fiber equivalence',()=>{
  for(const levels of [[0,0],[0,2]]) {
    const context=hypotheses(...levels);
    const term=equivalenceFromInverse(v('A'),v('B'),v('f'),v('g'),v('eta'),v('epsilon'));
    const type=equiv(v('A'),v('B'));
    const closed=close(term,context,T.lam),statement=close(type,context,T.pi);
    const result=checkKernel(closed,statement,[],{normalize:false});
    assert(result.ok,result.error);
    assert(result.arenaNodes<15000);
    assert(result.steps<100000);
  }
});

test('checked reference inputs and non-reflexivity-shaped homotopies feed actual Glue transport',()=>{
  const identity=T.lam('x',two,v('x'));
  const homotopy=T.lam('x',two,T.line('i',two,T.comp('j',two,[
    {face:F.endpoint('i',0),term:v('x')},{face:F.endpoint('i',1),term:v('x')},
  ],v('x'))));
  const ref=name=>({tag:'Ref',name});
  const definitions=[{name:'identity',value:identity},{name:'eta',value:homotopy},{name:'epsilon',value:homotopy}];
  const proof=equivalenceFromInverse(two,two,ref('identity'),ref('identity'),ref('eta'),ref('epsilon'));
  const checked=checkKernel(proof,equiv(two,two),[],{definitions,normalize:false});
  assert(checked.ok,checked.error);
  definitions.push({name:'equivalence',value:proof,type:equiv(two,two)});
  const ua=T.line('i',T.universe(0),T.glueType(two,[
    {face:F.endpoint('i',0),type:two,equiv:ref('equivalence')},
    {face:F.endpoint('i',1),type:two,equiv:identityEquivalence(two)},
  ]));
  const moved=T.comp('j',T.at(ua,I.variable('j')),[],right);
  const result=checkKernel(moved,two,[],{definitions});
  assert(result.ok,result.error);
  assert.deepEqual(result.normal,right);
});

test('wrong inverse laws do not become equivalence certificates',()=>{
  const identity=T.lam('x',two,v('x'));
  const constant=T.lam('x',two,left);
  const reflexivity=T.lam('x',two,T.line('i',two,v('x')));
  const wrong=equivalenceFromInverse(two,two,constant,identity,reflexivity,reflexivity);
  assert.equal(checkKernel(wrong,equiv(two,two),[],{normalize:false}).ok,false);
});
