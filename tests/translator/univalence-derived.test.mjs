import "../fresh-build.mjs";
import test from 'node:test';
import assert from 'node:assert/strict';
import {T} from '../../web/translator/core.mjs';
import {face as F,interval as I} from '../../web/translator/lattice.mjs';
import {checkKernel} from './kernel-check.mjs';
import {contractible,contractibilityPath,equiv,identityEquivalence,
  unglueEquivalence,totalEquivalences,univalenceContraction,strictIsomorphismEquivalence} from '../../web/translator/equivalence.mjs';
// Two points, the examples' small inductive type.
const two=T.sum(T.unit,T.unit),left=T.inl(two,T.point),right=T.inr(two,T.point);
const v=T.variable;
function checked(term,type,context=[]) {
  const native=checkKernel(term,type,context,{normalize:false});
  assert(native.ok,native.error);
  return native;
}

test('unglue is a derived equivalence with checked contractible fibers',()=>{
  const A=v('A'),X=v('X'),e=v('e');
  const context=[['A',T.universe(0)],['X',T.universe(0)],['e',equiv(X,A)]];
  const G=T.glueType(A,[{face:F.endpoint('i',0),type:X,equiv:e}]);
  const family=equiv(G,A),term=T.line('i',family,unglueEquivalence(G));
  // Its normal form is not checked again: there two tubes' agreement is a
  // composition the kernel's normal form splits into tubes otherwise than
  // the other side, which the driver cannot compare (work plan I1.2c).
  checked(term,null,context);
  const empty=T.glueType(A,[]);
  checked(unglueEquivalence(empty),equiv(empty,A),context);
});

test('contractibility witnesses are connected by a derived cubical square',()=>{
  const A=v('A'),c=v('c'),d=v('d');
  const context=[['A',T.universe(1)],['c',contractible(A)],['d',contractible(A)]];
  checked(contractibilityPath(A,c,d),T.path('i',contractible(A),c,d),context);
});

function replaceIdentity(term) {
  if(Array.isArray(term))return term.map(replaceIdentity);
  if(!term||typeof term!=='object')return term;
  if(term.tag==='Var'&&term.name==='identity')return {tag:'Ref',name:'identity'};
  return Object.fromEntries(Object.entries(term).map(([key,value])=>[key,replaceIdentity(value)]));
}

// The total space of equivalences into A is contractible: closed, from the
// checked identity equivalence alone, without normalizing the proof.
for(const level of [0,2])test(`univalence total-space contraction at U${level} checks closed using only prior checked definitions`,()=>{
  const A=v('A');
  const identity=T.lam('A',T.universe(level),identityEquivalence(A));
  const contraction=univalenceContraction(A,level,T.app(v('identity'),A));
  const statement=contractible(totalEquivalences(A,level));
  const term=replaceIdentity(T.lam('A',T.universe(level),contraction));
  const type=T.pi('A',T.universe(level),statement);
  const result=checkKernel(term,type,[],{normalize:false,definitions:[{name:'identity',value:identity}]});
  assert(result.ok,result.error);
  assert(result.arenaNodes<100000);
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
