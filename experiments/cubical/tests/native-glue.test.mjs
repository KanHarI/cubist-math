import test from 'node:test';
import assert from 'node:assert/strict';
import {Checker as ReferenceChecker,T} from '../core.mjs';
import {identityEquivalence,equiv} from '../equivalence.mjs';
import {face as F,interval as I} from '../lattice.mjs';
import {checkNative} from '../native.mjs';
class Checker {
  verify(term,type=null,ctx=[]) {
    const native=checkNative(term,type,ctx);
    if(!native.ok)throw Error(native.error);
    const reference=new ReferenceChecker({fuel:1000000}),expected=reference.verify(term,type,ctx);
    assert(reference.equal(native.type,expected.type));
    assert(reference.equal(native.normal,expected.normal));
    reference.verify(native.normal,expected.type,ctx);
    return native;
  }
  equal(a,b){return new ReferenceChecker().equal(a,b);}
}
const v=T.variable;
function ua(A,B,e) {
  return T.line('ua',T.universe(0),T.glueType(B,[
    {face:F.endpoint('ua',0),type:A,equiv:e},
    {face:F.endpoint('ua',1),type:B,equiv:identityEquivalence(B)},
  ]));
}
test('native: checked Glue forms a universe path from a genuine equivalence',()=>{
  const A=v('A'),B=v('B'),e=v('e');
  const ctx=[['A',T.universe(0)],['B',T.universe(0)],['e',equiv(A,B)]];
  const path=ua(A,B,e),check=new Checker();
  check.verify(path,T.path('i',T.universe(0),A,B),ctx);
  assert(check.equal(check.verify(T.at(path,I.zero),T.universe(0),ctx).normal,A));
  assert(check.equal(check.verify(T.at(path,I.one),T.universe(0),ctx).normal,B));
});
test('native: Glue checks the actual equivalence witness and rejects an arbitrary function',()=>{
  const bad=T.glueType(T.nat,[{face:F.top,type:T.nat,equiv:T.lam('x',T.nat,v('x'))}]);
  assert.throws(()=>new Checker().verify(bad),/Type mismatch/);
});
test('native: Glue introduction and projection compute with checked boundaries',()=>{
  const e=identityEquivalence(T.nat),G=T.glueType(T.nat,[{face:F.top,type:T.nat,equiv:e}]);
  const value=T.glue(G,T.zero,[{face:F.top,term:T.zero}]),check=new Checker();
  assert.deepEqual(check.verify(value,G).normal,T.zero);
  assert.deepEqual(check.verify(T.unglue(G,value),T.nat).normal,T.zero);
  assert.throws(()=>check.verify(T.glue(G,T.succ(T.zero),[{face:F.top,term:T.zero}]),G),/agree with its base/);
});
test('native: partial Glue retains its equivalence and computes unglue after glue',()=>{
  const G=T.glueType(T.nat,[{face:F.endpoint('i',0),type:T.nat,equiv:identityEquivalence(T.nat)}]);
  const value=T.glue(G,T.zero,[{face:F.endpoint('i',0),term:T.zero}]);
  const line=T.line('i',T.nat,T.unglue(G,value));
  assert.deepEqual(new Checker().verify(line).normal.body,T.zero);
});
test('native: Glue checks overlaps between partial equivalences',()=>{
  const A=v('A'),e=v('e'),f=v('f');
  const ctx=[['A',T.universe(0)],['e',equiv(A,A)],['f',equiv(A,A)]];
  const bad=T.line('i',T.universe(0),T.glueType(A,[
    {face:F.top,type:A,equiv:e},{face:F.endpoint('i',0),type:A,equiv:f},
  ]));
  assert.throws(()=>new Checker().verify(bad,null,ctx),/equivalences disagree/);
});
test('native: Glue composition executes transport along identity equivalence',()=>{
  const check=new Checker(),path=ua(T.nat,T.nat,identityEquivalence(T.nat));
  const moved=T.comp('j',T.at(path,I.variable('j')),[],T.succ(T.zero));
  const result=check.verify(moved,T.nat);
  assert.deepEqual(result.normal,T.succ(T.zero));
});
test('native: persistent gluing face and overlapping tube compute and recheck',()=>{
  const phi=F.endpoint('k',0),e=identityEquivalence(T.nat);
  const G=T.glueType(T.nat,[{face:phi,type:T.nat,equiv:e}]);
  const base=T.glue(G,T.zero,[{face:phi,term:T.zero}]);
  const comp=T.comp('i',G,[{face:phi,term:T.zero}],base);
  const check=new Checker(),result=check.verify(T.line('k',G,comp));
  check.verify(result.normal,result.type);
});
test('native: universe composition builds a checked Glue equivalence',()=>{
  const body=T.comp('i',T.universe(0),[{face:F.endpoint('k',0),term:T.nat}],T.nat);
  const check=new Checker(),result=check.verify(T.line('k',T.universe(0),body));
  check.verify(result.normal,result.type);
});
test('native: Glue eta reconstructs a neutral element',()=>{
  const G=T.glueType(T.nat,[{face:F.endpoint('k',0),type:T.nat,equiv:identityEquivalence(T.nat)}]);
  const g=v('g'),rebuilt=T.glue(G,T.unglue(G,g),[{face:F.endpoint('k',0),term:g}]);
  const body=T.lam('g',G,T.line('i',G,rebuilt));
  const expected=T.pi('g',G,T.path('i',G,g,g));
  new Checker().verify(T.line('k',expected,body));
});
test('native: empty gluing faces disappear before conversion',()=>{
  const empty=T.glueType(T.nat,[]),vacuous=T.glueType(T.nat,[{face:F.bottom,type:T.nat,equiv:identityEquivalence(T.nat)}]);
  const g=v('g'),proof=T.line('i',empty,g);
  new Checker().verify(proof,T.path('i',vacuous,g,g),[['g',empty]]);
});
