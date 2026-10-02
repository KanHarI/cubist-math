import "../../../tests/fresh-build.mjs";
import test from 'node:test';
import assert from 'node:assert/strict';
import {T} from '../core.mjs';
import {checkKernel} from './kernel-check.mjs';
import {withNativeReferences} from '../equivalence.mjs';
import {face as F} from '../lattice.mjs';
import {identityEquivalence} from '../equivalence.mjs';
import {pathRefl,pathInverse,pathApply,pathConcat,transportConstant,
  pathRightUnit,pathLeftUnit,pathInverseLeft,pathInverseRight,pathAssociative,pathApplyConcat} from '../path-algebra.mjs';
const v=T.variable;
const equality=(A,x,y)=>T.path('i',A,x,y);
test('native reference substitution keeps many references distinct and restores their identity',()=>{
  const references=Array.from({length:2048},(_,index)=>({tag:'Ref',name:`proof_${index}`}));
  const reserved=v('checked_reference_1');
  const restored=withNativeReferences([references,reserved],(symbolic,kept)=>{
    assert.equal(kept.name,reserved.name);
    assert.equal(new Set(symbolic.map(item=>item.name)).size,references.length);
    assert.ok(symbolic.every(item=>item.name!==reserved.name));
    return symbolic;
  });
  for(let index=0;index<references.length;index++)assert.equal(restored[index],references[index]);
});
function close(term,context,kind) {
  for(const [name,type]of [...context].reverse())term=kind(name,type,term);
  return term;
}
function checked(term,type,context) {
  term=close(term,context,T.lam);type=close(type,context,T.pi);
  const result=checkKernel(term,type,[],{normalize:false});
  assert(result.ok,result.error);
  return result;
}
for(const level of [0,2]) {
  test(`cubical units, inverse laws and constant transport at U${level}`,()=>{
    const A=v('A'),x=v('x'),y=v('y'),p=v('p');
    const P=equality(A,x,y);
    const context=[['A',T.universe(level)],['x',A],['y',A],['p',P]];
    const concat=(a,b)=>pathConcat(A,x,a,b);
    checked(transportConstant(A,x),equality(A,T.comp('j',A,[],x),x),context);
    checked(pathRightUnit(A,x,y,p),equality(P,concat(p,pathRefl(A,y)),p),context);
    checked(pathLeftUnit(A,x,y,p),equality(P,concat(pathRefl(A,x),p),p),context);
    checked(pathInverseRight(A,x,y,p),equality(equality(A,x,x),
      concat(p,pathInverse(A,p)),pathRefl(A,x)),context);
    checked(pathInverseLeft(A,x,y,p),equality(equality(A,y,y),
      pathConcat(A,y,pathInverse(A,p),p),pathRefl(A,y)),context);
  });
  test(`cubical concatenation is associative at U${level}`,()=>{
    const A=v('A'),x=v('x'),y=v('y'),z=v('z'),w=v('w');
    const p=v('p'),q=v('q'),r=v('r');
    const context=[['A',T.universe(level)],['x',A],['y',A],['z',A],['w',A],
      ['p',equality(A,x,y)],['q',equality(A,y,z)],['r',equality(A,z,w)]];
    const lhs=pathConcat(A,x,pathConcat(A,x,p,q),r);
    const rhs=pathConcat(A,x,p,pathConcat(A,y,q,r));
    checked(pathAssociative(A,x,y,z,w,p,q,r),equality(equality(A,x,w),lhs,rhs),context);
  });
}
test('direct application and reversal have their claimed endpoints',()=>{
  const A=v('A'),B=v('B'),f=v('f'),x=v('x'),y=v('y'),p=v('p');
  const context=[['A',T.universe(0)],['B',T.universe(2)],['f',T.pi('x',A,B)],
    ['x',A],['y',A],['p',equality(A,x,y)]];
  checked(pathApply(B,f,p),equality(B,T.app(f,x),T.app(f,y)),context);
  checked(pathInverse(A,p),equality(A,y,x),context);
});


test('groupoid laws apply to an actual univalence loop with named checked definitions',()=>{
  const ref=name=>({tag:'Ref',name}),Bool=T.sum(T.unit,T.unit),U=T.universe(0);
  const A=U,x=ref('bool'),p=ref('loop');
  // A Glue path from Bool to itself, along the identity equivalence.
  const glued=T.line('i',U,T.glueType(Bool,[
    {face:F.endpoint('i',0),type:Bool,equiv:identityEquivalence(Bool)},
    {face:F.endpoint('i',1),type:Bool,equiv:identityEquivalence(Bool)},
  ]));
  const definitions=[
    {name:'bool',value:Bool},
    {name:'first',value:T.line('i',U,ref('bool'))},
    {name:'second',value:glued},
    {name:'unit_path',value:T.line('i',U,T.unit)},
    {name:'loop',value:pathConcat(A,x,ref('first'),pathInverse(A,ref('second')))},
  ];
  const P=equality(A,x,x),c=(p,q)=>pathConcat(A,x,p,q);
  const cases=[
    [pathRightUnit(A,x,x,p),equality(P,c(p,pathRefl(A,x)),p)],
    [pathInverseRight(A,x,x,p),equality(P,c(p,pathInverse(A,p)),pathRefl(A,x))],
    [pathInverseLeft(A,x,x,p),equality(P,c(pathInverse(A,p),p),pathRefl(A,x))],
    [pathAssociative(A,x,x,x,x,p,p,p),equality(P,c(c(p,p),p),c(p,c(p,p)))],
  ];
  for(const [term,type]of cases) {
    const result=checkKernel(term,type,[],{definitions,normalize:false});
    assert(result.ok,result.error);
    assert(result.arenaNodes<10000);
  }
  // A path from Unit cannot follow one that ends at Bool.
  const malformed=pathConcat(A,x,ref('first'),ref('unit_path'));
  assert.equal(checkKernel(malformed,null,[],{definitions,normalize:false}).ok,false);
});

test('path algebra builders freshen colliding binder names',()=>{
  const A=v('path'),x=v('compose'),y=v('law'),p=v('inner');
  const context=[['path',T.universe(0)],['compose',A],['law',A],
    ['inner',equality(A,x,y)]];
  checked(pathInverseRight(A,x,y,p),equality(equality(A,x,x),
    pathConcat(A,x,p,pathInverse(A,p)),pathRefl(A,x)),context);
  const ref={tag:'DefRef',name:'checked_path'};
  assert(JSON.stringify(pathInverse(A,ref)).includes('"tag":"DefRef"'));
});

for(const [a,b]of [[0,0],[0,2],[2,0]])test(`ap preserves concatenation from U${a} to U${b}`,()=>{
  const A=v('A'),B=v('B'),f=v('f'),x=v('x'),y=v('y'),z=v('z'),p=v('p'),q=v('q');
  const context=[['A',T.universe(a)],['B',T.universe(b)],['f',T.pi('a',A,B)],
    ['x',A],['y',A],['z',A],['p',equality(A,x,y)],['q',equality(A,y,z)]];
  const lhs=pathApply(B,f,pathConcat(A,x,p,q));
  const rhs=pathConcat(B,T.app(f,x),pathApply(B,f,p),pathApply(B,f,q));
  checked(pathApplyConcat(A,B,f,x,y,z,p,q),equality(equality(B,T.app(f,x),T.app(f,z)),lhs,rhs),context);
});
