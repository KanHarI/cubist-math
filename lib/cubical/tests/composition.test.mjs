import test from "node:test";
import assert from "node:assert/strict";
import {Checker,T} from "../core.mjs";
import {interval as I,face as F} from "../lattice.mjs";
const v=T.variable,A=v("A"),a=v("a"),b=v("b"),c=v("c"),p=v("p"),q=v("q");
const path=(A,x,y)=>T.path("r",A,x,y),at=T.at;
const ctx=[["A",T.universe(0)],["a",A],["b",A],["c",A],["p",path(A,a,b)],["q",path(A,b,c)]];
const concat=T.line("j",A,T.comp("i",A,[
  {face:F.endpoint("j",0),term:a},
  {face:F.endpoint("j",1),term:at(q,I.variable("i"))},
],at(p,I.variable("j"))));
test("composition fills a box and constructs path concatenation",()=>{
  const check=new Checker();
  check.verify(concat,path(A,a,c),ctx);
  assert.deepEqual(check.verify(at(concat,I.zero),A,ctx).normal,a);
  assert.deepEqual(check.verify(at(concat,I.one),A,ctx).normal,c);
});
test("transport through the Nat and Unit constructor computations",()=>{
  const check=new Checker();
  assert.deepEqual(check.verify(T.comp("i",T.nat,[],T.succ(T.succ(T.zero))),T.nat).normal,T.succ(T.succ(T.zero)));
  assert.deepEqual(check.verify(T.comp("i",T.unit,[],T.point),T.unit).normal,T.point);
});
test("a tube covering the whole extent computes to its far endpoint",()=>{
  const check=new Checker();
  assert.deepEqual(check.verify(T.comp("i",A,[{face:F.top,term:at(p,I.variable("i"))}],a),A,ctx).normal,b);
});
test("tube/base disagreement is rejected",()=>{
  assert.throws(()=>new Checker().verify(T.comp("i",A,[{face:F.top,term:at(p,I.variable("i"))}],b),A,ctx),/disagrees with its base/);
});
test("all tube overlaps are checked, not just their initial endpoints",()=>{
  const bad=T.line("j",path(A,a,a),T.line("k",A,T.comp("i",A,[
    {face:F.endpoint("j",0),term:at(p,I.variable("i"))},
    {face:F.endpoint("k",0),term:a},
  ],a)));
  assert.throws(()=>new Checker().verify(bad,null,ctx),/disagree on an overlap/);
});
test("faces cannot depend on the direction being composed",()=>{
  assert.throws(()=>new Checker().verify(T.comp("i",A,[{face:F.endpoint("i",0),term:a}],a),A,ctx),/unbound dimension i/);
});
test("dimension substitution preserves a checked partial boundary",()=>{
  const check=new Checker();
  const reverse=T.line("k",A,at(concat,I.reverse(I.variable("k"))));
  check.verify(reverse,path(A,c,a),ctx);
  assert.deepEqual(check.verify(at(reverse,I.zero),A,ctx).normal,c);
});
test("Nat composition does not discard a nonconstructor tube",()=>{
  const check=new Checker(),npath=path(T.nat,T.zero,T.zero);
  const cube=T.line("j",T.nat,T.comp("i",T.nat,[{face:F.endpoint("j",0),term:at(p,I.variable("i"))}],T.zero));
  const result=check.verify(cube,npath,[["p",npath]]);
  assert.equal(result.normal.body.tag,"Comp");
});
test("composition through Path adds both endpoint faces and rechecks",()=>{
  const check=new Checker(), loopType=path(T.nat,T.zero,T.zero),refl=T.line("r",T.nat,T.zero);
  const result=check.verify(T.comp("i",loopType,[],refl),loopType);
  assert.equal(result.normal.tag,"PLam");
  assert.deepEqual(result.normal.body,T.zero);
  check.verify(result.normal,loopType);
});
test("Sigma composition fills the first coordinate before the dependent second",()=>{
  const check=new Checker(),type=T.sigma("n",T.nat,path(T.nat,v("n"),v("n")));
  const pair=T.pair(type,T.succ(T.zero),T.line("r",T.nat,T.succ(T.zero)));
  const result=check.verify(T.comp("i",type,[],pair),type);
  assert.deepEqual(result.normal.first,T.succ(T.zero));
  assert.deepEqual(result.normal.second.body,T.succ(T.zero));
  check.verify(result.normal,type);
});
test("Pi composition fills its domain backwards and computes on numerals",()=>{
  const check=new Checker(),type=T.pi("n",T.nat,T.nat),fn=T.lam("n",T.nat,T.succ(v("n")));
  const moved=T.comp("i",type,[],fn);
  const result=check.verify(T.app(moved,T.succ(T.zero)),T.nat);
  assert.deepEqual(result.normal,T.succ(T.succ(T.zero)));
  check.verify(check.verify(moved,type).normal,type);
});
