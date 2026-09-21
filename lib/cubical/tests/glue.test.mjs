import test from 'node:test';
import assert from 'node:assert/strict';
import {Checker,T} from '../core.mjs';
import {identityEquivalence,equiv} from '../equivalence.mjs';
import {face as F,interval as I} from '../lattice.mjs';
const v=T.variable;
function ua(A,B,e) {
  return T.line('ua',T.universe(0),T.glueType(B,[
    {face:F.endpoint('ua',0),type:A,equiv:e},
    {face:F.endpoint('ua',1),type:B,equiv:identityEquivalence(B)},
  ]));
}
test('checked Glue forms a universe path from a genuine equivalence',()=>{
  const A=v('A'),B=v('B'),e=v('e');
  const ctx=[['A',T.universe(0)],['B',T.universe(0)],['e',equiv(A,B)]];
  const path=ua(A,B,e),check=new Checker();
  check.verify(path,T.path('i',T.universe(0),A,B),ctx);
  assert(check.equal(check.verify(T.at(path,I.zero),T.universe(0),ctx).normal,A));
  assert(check.equal(check.verify(T.at(path,I.one),T.universe(0),ctx).normal,B));
});
test('Glue checks the actual equivalence witness and rejects an arbitrary function',()=>{
  const bad=T.glueType(T.nat,[{face:F.top,type:T.nat,equiv:T.lam('x',T.nat,v('x'))}]);
  assert.throws(()=>new Checker().verify(bad),/Type mismatch/);
});
test('Glue introduction and projection compute with checked boundaries',()=>{
  const e=identityEquivalence(T.nat),G=T.glueType(T.nat,[{face:F.top,type:T.nat,equiv:e}]);
  const value=T.glue(G,T.zero,[{face:F.top,term:T.zero}]),check=new Checker();
  assert.deepEqual(check.verify(value,G).normal,T.zero);
  assert.deepEqual(check.verify(T.unglue(G,value),T.nat).normal,T.zero);
  assert.throws(()=>check.verify(T.glue(G,T.succ(T.zero),[{face:F.top,term:T.zero}]),G),/agree with its base/);
});
test('partial Glue retains its equivalence and computes unglue after glue',()=>{
  const G=T.glueType(T.nat,[{face:F.endpoint('i',0),type:T.nat,equiv:identityEquivalence(T.nat)}]);
  const value=T.glue(G,T.zero,[{face:F.endpoint('i',0),term:T.zero}]);
  const line=T.line('i',T.nat,T.unglue(G,value));
  assert.deepEqual(new Checker().verify(line).normal.body,T.zero);
});
test('Glue checks overlaps between partial equivalences',()=>{
  const A=v('A'),e=v('e'),f=v('f');
  const ctx=[['A',T.universe(0)],['e',equiv(A,A)],['f',equiv(A,A)]];
  const bad=T.line('i',T.universe(0),T.glueType(A,[
    {face:F.top,type:A,equiv:e},{face:F.endpoint('i',0),type:A,equiv:f},
  ]));
  assert.throws(()=>new Checker().verify(bad,null,ctx),/equivalences disagree/);
});
test('Glue composition executes transport along the identity equivalence',()=>{
  const check=new Checker({fuel:1000000}),path=ua(T.nat,T.nat,identityEquivalence(T.nat));
  const moved=T.comp('j',T.at(path,I.variable('j')),[],T.succ(T.zero));
  const result=check.verify(moved,T.nat);
  assert.deepEqual(result.normal,T.succ(T.zero));
  check.verify(result.normal,T.nat);
});

test('Glue composition expansion independently typechecks before reducing',async()=>{
  const {glueComposition}=await import('../core.mjs');
  const check=new Checker({fuel:1000000}),e=identityEquivalence(T.nat);
  const family=T.glueType(T.nat,[
    {face:F.endpoint('i',0),type:T.nat,equiv:e},
    {face:F.endpoint('i',1),type:T.nat,equiv:e},
  ]);
  const raw=T.comp('i',family,[],T.succ(T.zero));
  const checked=check.infer(raw).term;
  const expansion=glueComposition({...checked,family:check.nf(checked.family)});
  assert.deepEqual(check.verify(expansion,T.nat).normal,T.succ(T.zero));
});

test('Glue composition checks a persistent face and its overlapping tube',async()=>{
  const {glueComposition}=await import('../core.mjs');
  const check=new Checker({fuel:1000000}),e=identityEquivalence(T.nat);
  const phi=F.endpoint('k',0),family=T.glueType(T.nat,[{face:phi,type:T.nat,equiv:e}]);
  const base=T.glue(family,T.zero,[{face:phi,term:T.zero}]);
  const comp=T.comp('i',family,[{face:phi,term:T.zero}],base);
  const checked=check.infer(comp,new Map(),new Set(['k'])).term;
  const expansion=glueComposition({...checked,family:check.nf(checked.family)});
  const line=T.line('k',family,expansion);
  const result=check.verify(line);
  check.verify(result.normal,result.type);
});

test('universe composition constructs a Glue type with a checked equivalence',async()=>{
  const {universeComposition}=await import('../core.mjs');
  const check=new Checker({fuel:1000000});
  const body=T.comp('i',T.universe(0),[{face:F.endpoint('k',0),term:T.nat}],T.nat);
  const checked=check.infer(body,new Map(),new Set(['k'])).term;
  const expansion=universeComposition(checked);
  const wrapped=T.line('k',T.universe(0),expansion);
  const result=check.verify(wrapped);
  check.verify(result.normal,result.type);
});
test('Glue eta reconstructs a neutral element from its face and projection',()=>{
  const check=new Checker({fuel:1000000});
  const G=T.glueType(T.nat,[{face:F.endpoint('k',0),type:T.nat,equiv:identityEquivalence(T.nat)}]);
  const g=v('g'),rebuilt=T.glue(G,T.unglue(G,g),[{face:F.endpoint('k',0),term:g}]);
  const body=T.lam('g',G,T.line('i',G,rebuilt));
  const expected=T.pi('g',G,T.path('i',G,g,g));
  check.verify(T.line('k',expected,body));
});
