import test from 'node:test';
import assert from 'node:assert/strict';
import {T,Checker} from '../core.mjs';
import {interval as I} from '../lattice.mjs';
import {equiv,strictIsomorphismEquivalence,univalencePath} from '../equivalence.mjs';
import {checkNative} from '../native.mjs';
import {dependentPathToTransport,transportToDependentPath,
  dependentPathTransportSection,dependentPathTransportRetraction,
  dependentPathTransportEquivalence} from '../path-over.mjs';
const v=T.variable;
function close(term,context,kind) {
  for(const [name,type]of [...context].reverse())term=kind(name,type,term);
  return term;
}
function generic(level) {
  const A=v('A'),B=v('B'),P=v('P'),a=v('a'),b=v('b');
  const family=T.at(P,I.variable('i'));
  const S=T.path('i',family,a,b),E=T.path('j',B,T.comp('i',family,[],a),b);
  const args=['i',family,a,b];
  const f=dependentPathToTransport(...args),g=transportToDependentPath(...args);
  const context=[['A',T.universe(level)],['B',T.universe(level)],
    ['P',T.path('i',T.universe(level),A,B)],['a',A],['b',B]];
  return {args,S,E,f,g,context};
}
function checkClosed(term,type,context) {
  term=close(term,context,T.lam);type=close(type,context,T.pi);
  const checker=new Checker({fuel:2000000});
  checker.check(term,checker.type(type,new Map(),new Set()).term,new Map(),new Set());
  const result=checkNative(term,type,[],{normalize:false});
  assert(result.ok,result.error);
  return result;
}
for(const level of [0,2]) {
  test(`dependent path / transport conversions and inverse laws at U${level}`,()=>{
    const {args,S,E,f,g,context}=generic(level);
    checkClosed(f,T.pi('p',S,E),context);
    checkClosed(g,T.pi('q',E,S),context);
    checkClosed(dependentPathTransportSection(...args),T.pi('p',S,
      T.path('k',S,T.app(g,T.app(f,v('p'))),v('p'))),context);
    checkClosed(dependentPathTransportRetraction(...args),T.pi('q',E,
      T.path('k',E,T.app(f,T.app(g,v('q'))),v('q'))),context);
  });
}
test('dependent path / transport bridge supplies checked contractible fibers',()=>{
  const {args,S,E,context}=generic(0);
  const result=checkClosed(dependentPathTransportEquivalence(...args),equiv(S,E),context);
  assert(result.ok,result.error);
});


test('nonconstant Glue family converts an actual transported endpoint using checked references',()=>{
  const ref=name=>({tag:'Ref',name});
  const A=T.sigma('n',T.nat,T.unit),B=T.sigma('u',T.unit,T.nat);
  const f=T.lam('p',A,T.pair(B,T.second(v('p')),T.first(v('p'))));
  const g=T.lam('q',B,T.pair(A,T.second(v('q')),T.first(v('q'))));
  const definitions=[{name:'A',value:A},{name:'B',value:B},
    {name:'e',value:strictIsomorphismEquivalence(A,B,f,g)},
    {name:'ua',value:univalencePath(ref('A'),ref('B'),ref('e'))},
    {name:'a',value:T.pair(A,T.succ(T.zero),T.point)}];
  const family=T.at(ref('ua'),I.variable('i')),a=ref('a');
  const b=T.comp('i',family,[],a);
  const args=['i',family,a,b];
  const S=T.path('i',family,a,b),E=T.path('j',ref('B'),b,b);
  const q=T.line('j',ref('B'),b);
  const p=T.app(transportToDependentPath(...args),q);
  assert(checkNative(p,S,[],{definitions,normalize:false}).ok);
  const roundtrip=T.app(dependentPathToTransport(...args),p);
  assert(checkNative(roundtrip,E,[],{definitions,normalize:false}).ok);
  const packaged=checkNative(dependentPathTransportEquivalence(...args),equiv(S,E),[],
    {definitions,normalize:false});
  assert(packaged.ok,packaged.error);
  assert(packaged.arenaNodes<30000);
  const bad=T.path('i',family,a,T.pair(B,T.point,T.zero));
  assert.equal(checkNative(p,bad,[],{definitions,normalize:false}).ok,false);
});

test('builders preserve native reference tags and avoid names already used by the caller',()=>{
  const {args,S,E,context}=generic(0);
  // Deliberately collide with every ordinary helper binder stem.
  const rename={A:'over',B:'along',P:'homotopy',a:'dependent_path',b:'transport_equality'};
  const rewrite=value=>{
    if(Array.isArray(value))return value.map(rewrite);
    if(!value||typeof value!=='object')return value;
    return Object.fromEntries(Object.entries(value).map(([key,item])=>
      [key,key==='name'&&rename[item]?rename[item]:rewrite(item)]));
  };
  const colliding=args.map(rewrite);
  checkClosed(dependentPathTransportEquivalence(...colliding),rewrite(equiv(S,E)),
    context.map(([name,type])=>[rename[name],rewrite(type)]));
  const tagged={tag:'DefRef',name:'family'};
  const output=dependentPathToTransport('i',T.at(tagged,I.variable('i')),v('a'),v('b'));
  const serialized=JSON.stringify(output);
  assert(serialized.includes('"tag":"DefRef","name":"family"'));
  assert(!serialized.includes('checked_reference'));
});

test('bridge keeps a large natural endpoint compact',()=>{
  const ref=name=>({tag:'Ref',name}),motive=T.lam('n',T.nat,T.nat);
  const double=T.lam('n',T.nat,T.natrec(motive,T.zero,
    T.lam('p',T.nat,T.lam('ih',T.nat,T.succ(T.succ(v('ih'))))),v('n')));
  const power=T.lam('n',T.nat,T.natrec(motive,T.succ(T.zero),
    T.lam('p',T.nat,T.lam('ih',T.nat,T.app(ref('double'),v('ih')))),v('n')));
  let twentyTwo=T.zero;
  for(let n=0;n<22;n++)twentyTwo=T.succ(twentyTwo);
  const definitions=[{name:'double',value:double},{name:'power',value:power},
    {name:'huge',value:T.app(ref('power'),twentyTwo)}];
  const a=ref('huge'),S=T.path('i',T.nat,a,a);
  const E=T.path('j',T.nat,T.comp('i',T.nat,[],a),a);
  const result=checkNative(dependentPathTransportEquivalence('i',T.nat,a,a),
    equiv(S,E),[],{definitions,normalize:false});
  assert(result.ok,result.error);
  assert(result.arenaNodes<15000);
  assert(result.reductionSteps<100000);
});
