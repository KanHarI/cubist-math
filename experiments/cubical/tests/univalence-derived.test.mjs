import test from 'node:test';
import assert from 'node:assert/strict';
import {Checker,T} from '../core.mjs';
import {face as F} from '../lattice.mjs';
import {checkNative} from '../native.mjs';
import {contractible,contractibilityPath,equiv,identityEquivalence,
  unglueEquivalence,totalEquivalences,univalenceContraction} from '../equivalence.mjs';
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
