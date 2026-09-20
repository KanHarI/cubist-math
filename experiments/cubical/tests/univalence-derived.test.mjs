import test from 'node:test';
import assert from 'node:assert/strict';
import {Checker,T} from '../core.mjs';
import {face as F,interval as I} from '../lattice.mjs';
import {checkNative} from '../native.mjs';
import {contractible,contractibilityPath,equiv,identityEquivalence,
  unglueEquivalence,totalEquivalences,univalenceContraction,strictIsomorphismEquivalence} from '../equivalence.mjs';
const v=T.variable;
function checked(term,type,context=[]) {
  const js=new Checker({fuel:2000000}),ctx=new Map();
  for(const [name,raw]of context)ctx.set(name,js.type(raw,ctx,new Set()).term);
  if(type)js.check(term,js.type(type,ctx,new Set()).term,ctx,new Set());
  else js.infer(term,ctx,new Set());
  const native=checkNative(term,type,context,{normalize:false});
  assert(native.ok,native.error);
  return native;
}

test('unglue is a derived equivalence with checked contractible fibers',()=>{
  const A=v('A'),X=v('X'),e=v('e');
  const context=[['A',T.universe(0)],['X',T.universe(0)],['e',equiv(X,A)]];
  const G=T.glueType(A,[{face:F.endpoint('i',0),type:X,equiv:e}]);
  const family=equiv(G,A),term=T.line('i',family,unglueEquivalence(G));
  const result=checked(term,null,context);
  assert(checkNative(result.normal,result.type,context,{normalize:false}).ok);
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

for(const level of [0,2])test(`univalence total-space contraction at U${level} checks closed using only prior checked definitions`,()=>{
  const A=v('A');
  const identity=T.lam('A',T.universe(level),identityEquivalence(A));
  const idApplication=T.app(v('identity'),A);
  const contraction=univalenceContraction(A,level,idApplication);
  const statement=contractible(totalEquivalences(A,level));
  // Reference checks the same compositional proof using a previously checked
  // identity-equivalence function, without strongly normalizing the proof body.
  const reference=new Checker({fuel:2000000});
  const identityType=reference.infer(identity,new Map(),new Set()).type;
  const context=new Map([['identity',identityType],['A',T.universe(level)]]);
  reference.check(contraction,statement,context,new Set());
  // Native registration independently certifies the identity definition; the
  // final forall-A theorem is closed and carries no assumption telescope.
  const term=replaceIdentity(T.lam('A',T.universe(level),contraction));
  const type=T.pi('A',T.universe(level),statement);
  const result=checkNative(term,type,[],{normalize:false,
    definitions:[{name:'identity',value:identity}]});
  assert(result.ok,result.error);
  assert(result.arenaNodes<100000);
  assert(result.reductionSteps<5000000);
});

test('actual univalence transport computes a nonidentity product-swap equivalence',()=>{
  const A=T.sigma('n',T.nat,T.unit),B=T.sigma('u',T.unit,T.nat);
  const forward=T.lam('p',A,T.pair(B,T.second(v('p')),T.first(v('p'))));
  const inverse=T.lam('q',B,T.pair(A,T.second(v('q')),T.first(v('q'))));
  const e=strictIsomorphismEquivalence(A,B,forward,inverse);
  checked(e,equiv(A,B));
  const ua=T.line('i',T.universe(0),T.glueType(B,[
    {face:F.endpoint('i',0),type:A,equiv:e},
    {face:F.endpoint('i',1),type:B,equiv:identityEquivalence(B)},
  ]));
  const input=T.pair(A,T.succ(T.zero),T.point);
  const moved=T.comp('j',T.at(ua,I.variable('j')),[],input);
  const native=checkNative(moved,B);
  assert(native.ok,native.error);
  assert.deepEqual(native.normal.first,T.point);
  assert.deepEqual(native.normal.second,T.succ(T.zero));
  const reference=new Checker({fuel:2000000});
  const expected=reference.verify(moved,B);
  assert(reference.equal(native.normal,expected.normal));
  reference.verify(native.normal,B);
  assert(checkNative(native.normal,B,[],{normalize:false}).ok);
  const notInverse=T.lam('q',B,T.pair(A,T.zero,T.point));
  assert.equal(checkNative(strictIsomorphismEquivalence(A,B,forward,notInverse),equiv(A,B),[],{normalize:false}).ok,false);
});
