import "../fresh-build.mjs";
import test from 'node:test';
import assert from 'node:assert/strict';
import {T} from '../../web/translator/core.mjs';
import {identityEquivalence,equiv} from '../../web/translator/equivalence.mjs';
import {face as F,interval as I} from '../../web/translator/lattice.mjs';
import {checkKernel} from './kernel-check.mjs';
// The kernel checks the term, and its normal form checks at the same type.
class Kernel {
  verify(term,type=null,ctx=[]) {
    const native=checkKernel(term,type,ctx);
    if(!native.ok)throw Error(native.error);
    const again=checkKernel(native.normal,native.type,ctx);
    assert(again.ok,again.error);
    return native;
  }
}
const v=T.variable;
// Two points, the examples' small inductive type.
const two=T.sum(T.unit,T.unit),left=T.inl(two,T.point),right=T.inr(two,T.point);
function ua(A,B,e) {
  return T.line('ua',T.universe(0),T.glueType(B,[
    {face:F.endpoint('ua',0),type:A,equiv:e},
    {face:F.endpoint('ua',1),type:B,equiv:identityEquivalence(B)},
  ]));
}
test('checked Glue forms a universe path from a genuine equivalence',()=>{
  const A=v('A'),B=v('B'),e=v('e');
  const ctx=[['A',T.universe(0)],['B',T.universe(0)],['e',equiv(A,B)]];
  const path=ua(A,B,e),check=new Kernel();
  check.verify(path,T.path('i',T.universe(0),A,B),ctx);
  assert.deepEqual(check.verify(T.at(path,I.zero),T.universe(0),ctx).normal,A);
  assert.deepEqual(check.verify(T.at(path,I.one),T.universe(0),ctx).normal,B);
});
test('Glue checks the actual equivalence witness and rejects an arbitrary function',()=>{
  const bad=T.glueType(two,[{face:F.top,type:two,equiv:T.lam('x',two,v('x'))}]);
  assert.throws(()=>new Kernel().verify(bad),/Type mismatch/);
});
test('Glue introduction and projection compute with checked boundaries',()=>{
  const e=identityEquivalence(two),G=T.glueType(two,[{face:F.top,type:two,equiv:e}]);
  const value=T.glue(G,left,[{face:F.top,term:left}]),check=new Kernel();
  assert.deepEqual(check.verify(value,G).normal,left);
  assert.deepEqual(check.verify(T.unglue(G,value),two).normal,left);
  assert.throws(()=>check.verify(T.glue(G,right,[{face:F.top,term:left}]),G),/disagrees with the base/);
});
test('partial Glue retains its equivalence and computes unglue after glue',()=>{
  const G=T.glueType(two,[{face:F.endpoint('i',0),type:two,equiv:identityEquivalence(two)}]);
  const value=T.glue(G,left,[{face:F.endpoint('i',0),term:left}]);
  const line=T.line('i',two,T.unglue(G,value));
  assert.deepEqual(new Kernel().verify(line).normal.body,left);
});
test('Glue checks overlaps between partial equivalences',()=>{
  const A=v('A'),e=v('e'),f=v('f');
  const ctx=[['A',T.universe(0)],['e',equiv(A,A)],['f',equiv(A,A)]];
  const bad=T.line('i',T.universe(0),T.glueType(A,[
    {face:F.top,type:A,equiv:e},{face:F.endpoint('i',0),type:A,equiv:f},
  ]));
  assert.throws(()=>new Kernel().verify(bad,null,ctx),/disagree where their faces meet/);
});
test('Glue composition executes transport along identity equivalence',()=>{
  const check=new Kernel(),path=ua(two,two,identityEquivalence(two));
  const moved=T.comp('j',T.at(path,I.variable('j')),[],right);
  const result=check.verify(moved,two);
  assert.deepEqual(result.normal,right);
});
test('persistent gluing face and overlapping tube compute and recheck',()=>{
  const phi=F.endpoint('k',0),e=identityEquivalence(two);
  const G=T.glueType(two,[{face:phi,type:two,equiv:e}]);
  const base=T.glue(G,left,[{face:phi,term:left}]);
  const comp=T.comp('i',G,[{face:phi,term:left}],base);
  const check=new Kernel(),result=check.verify(T.line('k',G,comp));
  check.verify(result.normal,result.type);
});
test('universe composition builds a checked Glue equivalence',()=>{
  const body=T.comp('i',T.universe(0),[{face:F.endpoint('k',0),term:two}],two);
  const check=new Kernel(),result=check.verify(T.line('k',T.universe(0),body));
  check.verify(result.normal,result.type);
});
// The tube is g itself, on a face other than the whole cube. g's type is
// the Glue type, which mentions k; on the face it is the glued type, and
// Restrict types g there, as Endpoint cannot while g depends on k.
test('Glue eta reconstructs a neutral element',()=>{
  const G=T.glueType(two,[{face:F.endpoint('k',0),type:two,equiv:identityEquivalence(two)}]);
  const g=v('g'),rebuilt=T.glue(G,T.unglue(G,g),[{face:F.endpoint('k',0),term:g}]);
  const body=T.lam('g',G,T.line('i',G,rebuilt));
  const expected=T.pi('g',G,T.path('i',G,g,g));
  new Kernel().verify(T.line('k',expected,body));
});
test('empty gluing faces disappear before conversion',()=>{
  const empty=T.glueType(two,[]),vacuous=T.glueType(two,[{face:F.bottom,type:two,equiv:identityEquivalence(two)}]);
  const g=v('g'),proof=T.line('i',empty,g);
  new Kernel().verify(proof,T.path('i',vacuous,g,g),[['g',empty]]);
});
