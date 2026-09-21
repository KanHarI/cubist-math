import test from 'node:test';
import assert from 'node:assert/strict';
import {T,Checker} from '../core.mjs';
import {interval as I} from '../lattice.mjs';
import {equiv,identityEquivalence,strictIsomorphismEquivalence,
  univalencePath,univalenceTransportBeta} from '../equivalence.mjs';
import {checkNative} from '../native.mjs';
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
    const reference=new Checker({fuel:2000000});
    reference.check(term,reference.type(type,new Map(),new Set()).term,new Map(),new Set());
    const result=checkNative(term,type,[],{normalize:false});
    assert(result.ok,result.error);
    assert(result.arenaNodes<10000);
    assert(result.reductionSteps<100000);
  }
});

test('ua beta relates actual nonidentity transport to its named forward map',()=>{
  const A=T.sigma('n',T.nat,T.unit),B=T.sigma('u',T.unit,T.nat);
  const forward=T.lam('p',A,T.pair(B,T.second(v('p')),T.first(v('p'))));
  const inverse=T.lam('q',B,T.pair(A,T.second(v('q')),T.first(v('q'))));
  const definitions=[{name:'A',value:A},{name:'B',value:B},
    {name:'e',value:strictIsomorphismEquivalence(A,B,forward,inverse)},
    {name:'x',value:T.pair(A,T.succ(T.zero),T.point)}];
  const inputs=[ref('A'),ref('B'),ref('e'),ref('x')];
  const term=univalenceTransportBeta(...inputs);
  const result=checkNative(term,betaType(...inputs),[],{definitions,normalize:false});
  assert(result.ok,result.error);
  const wrong=T.path('i',B,transport(...inputs),T.pair(B,T.point,T.zero));
  assert.equal(checkNative(term,wrong,[],{definitions,normalize:false}).ok,false);
});

test('ua beta keeps a compact argument denoting over four million unary successors',()=>{
  const motive=T.lam('n',T.nat,T.nat),one=T.succ(T.zero);
  const double=T.lam('n',T.nat,T.natrec(motive,T.zero,
    T.lam('p',T.nat,T.lam('ih',T.nat,T.succ(T.succ(v('ih'))))),v('n')));
  const power=T.lam('n',T.nat,T.natrec(motive,one,
    T.lam('p',T.nat,T.lam('ih',T.nat,T.app(ref('double'),v('ih')))),v('n')));
  let twentyTwo=T.zero;
  for(let i=0;i<22;i++)twentyTwo=T.succ(twentyTwo);
  const definitions=[{name:'double',value:double},{name:'power',value:power},
    {name:'huge',value:T.app(ref('power'),twentyTwo)},
    {name:'e',value:identityEquivalence(T.nat)}];
  const inputs=[T.nat,T.nat,ref('e'),ref('huge')];
  const result=checkNative(univalenceTransportBeta(...inputs),betaType(...inputs),[],{definitions,normalize:false});
  assert(result.ok,result.error);
  assert(result.arenaNodes<10000);
  assert(result.reductionSteps<100000);
});
