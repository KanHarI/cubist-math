import "../../../tests/fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {T} from "../core.mjs";
import {interval as I,face as F} from "../lattice.mjs";
import {checkKernel} from "./kernel-check.mjs";
// The kernel checks the term, and its normal form checks at the same type.
class Kernel {
  verify(term,type=null,ctx=[]) {
    const result=checkKernel(term,type,ctx);
    if(!result.ok)throw Error(result.error);
    const again=checkKernel(result.normal,result.type,ctx);
    assert(again.ok,again.error);
    return result;
  }
}
// Two points, the examples' small inductive type, and a function swapping them.
const two=T.sum(T.unit,T.unit),left=T.inl(two,T.point),right=T.inr(two,T.point);
const swap=x=>T.sumrec(T.lam("_",two,two),T.lam("u",T.unit,right),T.lam("u",T.unit,left),x);
const v=T.variable,A=v("A"),a=v("a"),b=v("b"),c=v("c"),p=v("p"),q=v("q");
const path=(A,x,y)=>T.path("r",A,x,y),at=T.at;
const ctx=[["A",T.universe(0)],["a",A],["b",A],["c",A],["p",path(A,a,b)],["q",path(A,b,c)]];
const concat=T.line("j",A,T.comp("i",A,[
  {face:F.endpoint("j",0),term:a},
  {face:F.endpoint("j",1),term:at(q,I.variable("i"))},
],at(p,I.variable("j"))));
test("composition fills a box and constructs path concatenation",()=>{
  const check=new Kernel();
  check.verify(concat,path(A,a,c),ctx);
  assert.deepEqual(check.verify(at(concat,I.zero),A,ctx).normal,a);
  assert.deepEqual(check.verify(at(concat,I.one),A,ctx).normal,c);
});
test("transport through the Sum and Unit constructor computations",()=>{
  const check=new Kernel();
  assert.deepEqual(check.verify(T.comp("i",two,[],right),two).normal,right);
  assert.deepEqual(check.verify(T.comp("i",T.unit,[],T.point),T.unit).normal,T.point);
});
test("a tube covering the whole extent computes to its far endpoint",()=>{
  const check=new Kernel();
  assert.deepEqual(check.verify(T.comp("i",A,[{face:F.top,term:at(p,I.variable("i"))}],a),A,ctx).normal,b);
});
test("tube/base disagreement is rejected",()=>{
  assert.throws(()=>new Kernel().verify(T.comp("i",A,[{face:F.top,term:at(p,I.variable("i"))}],b),A,ctx),/disagrees with its base/);
});
test("all tube overlaps are checked, not just their initial endpoints",()=>{
  const bad=T.line("j",path(A,a,a),T.line("k",A,T.comp("i",A,[
    {face:F.endpoint("j",0),term:at(p,I.variable("i"))},
    {face:F.endpoint("k",0),term:a},
  ],a)));
  assert.throws(()=>new Kernel().verify(bad,null,ctx),/disagree where their faces meet/);
});
test("faces cannot depend on the direction being composed",()=>{
  assert.throws(()=>new Kernel().verify(T.comp("i",A,[{face:F.endpoint("i",0),term:a}],a),A,ctx),/unbound.*dimension: i/i);
});
test("dimension substitution preserves a checked partial boundary",()=>{
  const check=new Kernel();
  const reverse=T.line("k",A,at(concat,I.reverse(I.variable("k"))));
  check.verify(reverse,path(A,c,a),ctx);
  assert.deepEqual(check.verify(at(reverse,I.zero),A,ctx).normal,c);
});
test("Sum composition does not discard a nonconstructor tube",()=>{
  const check=new Kernel(),npath=path(two,left,left);
  const cube=T.line("j",two,T.comp("i",two,[{face:F.endpoint("j",0),term:at(p,I.variable("i"))}],left));
  const result=check.verify(cube,npath,[["p",npath]]);
  assert.equal(result.normal.body.tag,"Comp");
});
test("composition through Path adds both endpoint faces and rechecks",()=>{
  const check=new Kernel(), loopType=path(two,left,left),refl=T.line("r",two,left);
  const result=check.verify(T.comp("i",loopType,[],refl),loopType);
  assert.equal(result.normal.tag,"PLam");
  assert.deepEqual(result.normal.body,left);
  check.verify(result.normal,loopType);
});
test("Sigma composition fills the first coordinate before the dependent second",()=>{
  const check=new Kernel(),type=T.sigma("n",two,path(two,v("n"),v("n")));
  const pair=T.pair(type,right,T.line("r",two,right));
  const result=check.verify(T.comp("i",type,[],pair),type);
  assert.deepEqual(result.normal.first,right);
  assert.deepEqual(result.normal.second.body,right);
  check.verify(result.normal,type);
});
test("Pi composition fills its domain backwards and computes on constructors",()=>{
  const check=new Kernel(),type=T.pi("n",two,two),fn=T.lam("n",two,swap(v("n")));
  const moved=T.comp("i",type,[],fn);
  const result=check.verify(T.app(moved,left),two);
  assert.deepEqual(result.normal,right);
  check.verify(check.verify(moved,type).normal,type);
});
test("neutral path composition retains and rechecks both endpoint walls",()=>{
  const check=new Kernel(),type=path(A,a,b);
  const result=check.verify(T.comp("i",type,[],p),type,ctx);
  assert.equal(result.normal.tag,"PLam");
  check.verify(result.normal,type,ctx);
});
test("function transport handles a genuinely varying domain",()=>{
  const check=new Kernel(),P=v("P"),ft=T.pi("n",two,two);
  const local=[["P",path(T.universe(0),two,T.unit)],["f",ft]];
  const family=T.pi("x",at(P,I.variable("i")),two);
  const result=check.verify(T.comp("i",family,[],v("f")),T.pi("x",T.unit,two),local);
  check.verify(result.normal,T.pi("x",T.unit,two),local);
});
