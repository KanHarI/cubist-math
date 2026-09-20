import test from 'node:test';
import assert from 'node:assert/strict';
import {T,Checker} from '../core.mjs';
import {face as F,interval as I} from '../lattice.mjs';
import {equiv,equivalenceFromInverse,identityEquivalence} from '../equivalence.mjs';
import {checkNative} from '../native.mjs';
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
    const reference=new Checker({fuel:2000000});
    const closed=close(term,context,T.lam),statement=close(type,context,T.pi);
    reference.check(closed,reference.type(statement,new Map(),new Set()).term,new Map(),new Set());
    const result=checkNative(closed,statement,[],{normalize:false});
    assert(result.ok,result.error);
    assert(result.arenaNodes<15000);
    assert(result.reductionSteps<100000);
  }
});

test('checked reference inputs and non-reflexivity-shaped homotopies feed actual Glue transport',()=>{
  const identity=T.lam('x',T.nat,v('x'));
  const homotopy=T.lam('x',T.nat,T.line('i',T.nat,T.comp('j',T.nat,[
    {face:F.endpoint('i',0),term:v('x')},{face:F.endpoint('i',1),term:v('x')},
  ],v('x'))));
  const ref=name=>({tag:'Ref',name});
  const definitions=[{name:'identity',value:identity},{name:'eta',value:homotopy},{name:'epsilon',value:homotopy}];
  const proof=equivalenceFromInverse(T.nat,T.nat,ref('identity'),ref('identity'),ref('eta'),ref('epsilon'));
  const checked=checkNative(proof,equiv(T.nat,T.nat),[],{definitions,normalize:false});
  assert(checked.ok,checked.error);
  definitions.push({name:'equivalence',value:proof,type:equiv(T.nat,T.nat)});
  const ua=T.line('i',T.universe(0),T.glueType(T.nat,[
    {face:F.endpoint('i',0),type:T.nat,equiv:ref('equivalence')},
    {face:F.endpoint('i',1),type:T.nat,equiv:identityEquivalence(T.nat)},
  ]));
  const moved=T.comp('j',T.at(ua,I.variable('j')),[],T.succ(T.zero));
  const result=checkNative(moved,T.nat,[],{definitions});
  assert(result.ok,result.error);
  assert.deepEqual(result.normal,T.succ(T.zero));
});

test('wrong inverse laws do not become equivalence certificates',()=>{
  const identity=T.lam('x',T.nat,v('x'));
  const constant=T.lam('x',T.nat,T.zero);
  const reflexivity=T.lam('x',T.nat,T.line('i',T.nat,v('x')));
  const wrong=equivalenceFromInverse(T.nat,T.nat,constant,identity,reflexivity,reflexivity);
  assert.equal(checkNative(wrong,equiv(T.nat,T.nat),[],{normalize:false}).ok,false);
});
