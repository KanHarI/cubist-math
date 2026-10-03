import "../../../tests/fresh-build.mjs";
import test from 'node:test';
import assert from 'node:assert/strict';
import {T} from '../core.mjs';
import {interval as I} from '../lattice.mjs';
import {equiv,identityEquivalence,strictIsomorphismEquivalence,
  univalencePath,univalenceTransportBeta} from '../equivalence.mjs';
import {checkKernel} from './kernel-check.mjs';
// Two points, the examples' small inductive type.
const two=T.sum(T.unit,T.unit),left=T.inl(two,T.point),right=T.inr(two,T.point);
const v=T.variable,ref=name=>({tag:'Ref',name});
const transport=(A,B,e,x,level=0)=>T.comp('j',T.at(univalencePath(A,B,e,level),I.variable('j')),[],x);
const betaType=(A,B,e,x,level=0)=>T.path('i',B,transport(A,B,e,x,level),T.app(T.first(e),x));
function close(term,context,kind) {
  for(const [name,type]of [...context].reverse())term=kind(name,type,term);
  return term;
}

test('ua transport beta is a closed derived theorem at explicit universe levels',()=>{
  for(const [a,b]of [[0,0],[0,2],[2,0]]) {
    const A=v('A'),B=v('B'),e=v('e'),x=v('x');
    const context=[['A',T.universe(a)],['B',T.universe(b)],['e',equiv(A,B)],['x',A]];
    const term=close(univalenceTransportBeta(A,B,e,x),context,T.lam);
    const type=close(betaType(A,B,e,x,Math.max(a,b)),context,T.pi);
    const result=checkKernel(term,type,[],{normalize:false});
    assert(result.ok,result.error);
    assert(result.arenaNodes<10000);
    assert(result.steps<100000);
  }
});

test('ua beta relates actual nonidentity transport to its named forward map',()=>{
  const A=T.sigma('n',two,T.unit),B=T.sigma('u',T.unit,two);
  const forward=T.lam('p',A,T.pair(B,T.second(v('p')),T.first(v('p'))));
  const inverse=T.lam('q',B,T.pair(A,T.second(v('q')),T.first(v('q'))));
  const definitions=[{name:'A',value:A},{name:'B',value:B},
    {name:'e',value:strictIsomorphismEquivalence(A,B,forward,inverse)},
    {name:'x',value:T.pair(A,right,T.point)}];
  const inputs=[ref('A'),ref('B'),ref('e'),ref('x')];
  const term=univalenceTransportBeta(...inputs);
  const result=checkKernel(term,betaType(...inputs),[],{definitions,normalize:false});
  assert(result.ok,result.error);
  const wrong=T.path('i',B,transport(...inputs),T.pair(B,T.point,left));
  assert.equal(checkKernel(term,wrong,[],{definitions,normalize:false}).ok,false);
});

