import "../../../tests/fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {T} from "../core.mjs";
import {interval as I} from "../lattice.mjs";
import {checkKernel} from "./kernel-check.mjs";
const v=T.variable,app=T.app,path=(A,a,b)=>T.path("i",A,a,b);
// Two points, the examples' small inductive type.
const two=T.sum(T.unit,T.unit),left=T.inl(two,T.point),right=T.inr(two,T.point);
// The kernel checks the term, at the expected normal form when one is given,
// and the normal form checks at the same type.
function agree(term,type=null,ctx=[],normal=undefined){
  const native=checkKernel(term,type,ctx);
  assert(native.ok,native.error);
  if(normal!==undefined)assert.deepEqual(native.normal,normal);
  const again=checkKernel(native.normal,native.type,ctx);
  assert(again.ok,again.error);
  return native;
}
test("dependent Pi/Sigma checking and reduction",()=>{
  const pairs=T.sigma("_",two,two);
  agree(app(T.lam("b",two,T.pair(pairs,v("b"),v("b"))),left),pairs,[],T.pair(pairs,left,left));
  const sigma=T.sigma("A",T.universe(0),v("A"));
  agree(T.second(T.pair(sigma,two,right)),two,[],right);
  agree(two,T.universe(0));
  assert.equal(checkKernel(two,T.universe(2)).ok,true);
  assert.equal(checkKernel(T.universe(1),T.universe(1)).ok,false);
});
test("path endpoints, reversal and dependent families",()=>{
  const A=v("A"),a=v("a"),b=v("b"),p=v("p"),ctx=[["A",T.universe(0)],["a",A],["b",A],["p",path(A,a,b)]];
  agree(T.at(p,I.zero),A,ctx,a);agree(T.at(p,I.one),A,ctx,b);
  agree(T.line("j",A,T.at(p,I.reverse(I.variable("j")))),path(A,b,a),ctx);
  const P=v("P"),q=v("q"),dep=[["P",path(T.universe(0),two,T.unit)],["q",T.path("j",T.at(P,I.variable("j")),left,T.point)]];
  agree(T.at(q,I.one),T.unit,dep,T.point);
});
test("computational dependent FunExt uses no axiom",()=>{
  const A=v("A"),B=v("B"),x=v("x"),f=v("f"),g=v("g"),Bx=app(B,x),ft=T.pi("x",A,Bx);
  const ht=T.pi("x",A,path(Bx,app(f,x),app(g,x)));
  const ctx=[["A",T.universe(0)],["B",T.pi("z",A,T.universe(0))],["f",ft],["g",ft],["h",ht]];
  agree(T.line("j",ft,T.lam("x",A,T.at(app(v("h"),x),I.variable("j")))),path(ft,f,g),ctx);
});
test("checker rejects forged endpoint claims and unbound variables",()=>{
  assert.equal(checkKernel(T.line("j",two,left),path(two,left,right)).ok,false);
  agree(T.comp("i",two,[],left),two);
  assert.equal(checkKernel(v("missing")).ok,false);
});

test("dependent Sum, Unit and Void rules",()=>{
  const l=left,r=right;
  const family=T.lam("tag",two,T.sumrec(T.lam("_",two,T.universe(0)),T.lam("_",T.unit,two),T.lam("_",T.unit,T.unit),v("tag")));
  agree(T.sumrec(family,T.lam("u",T.unit,right),T.lam("u",T.unit,T.point),l),two,[],right);
  agree(T.sumrec(family,T.lam("u",T.unit,right),T.lam("u",T.unit,T.point),r),T.unit,[],T.point);
  agree(T.unitrec(T.lam("u",T.unit,path(T.unit,v("u"),v("u"))),T.line("i",T.unit,T.point),T.point));
  agree(T.abort(two,v("impossible")),two,[["impossible",T.void]]);
  assert.equal(checkKernel(T.abort(two,T.point)).ok,false);
  assert.equal(checkKernel(T.sumrec(family,T.lam("u",T.unit,T.point),T.lam("u",T.unit,T.point),l)).ok,false);
});

test("checking preserves a shared application graph",()=>{
  const f=v("f"),context=[["f",T.pi("x",two,T.pi("y",two,two))],["n",two]];
  let term=v("n");
  for(let i=0;i<22;i++)term=app(app(f,term),term);
  const result=checkKernel(term,two,context);
  assert.equal(result.ok,true,result.error);
  assert.equal(result.normal.fn.arg,result.normal.arg);
  assert.deepEqual(result.type,two);
});

test("deeply nested constant paths check",()=>{
  let type=T.unit,value=T.point;
  for(let i=0;i<18;i++) {
    const oldType=type,oldValue=value;
    value=T.line("i",oldType,oldValue);
    type=T.path("i",oldType,oldValue,oldValue);
  }
  const result=checkKernel(value,type);
  assert.equal(result.ok,true,result.error);
  assert.equal(result.normal.tag,"PLam");
});

test("term substitution also avoids capture of free dimensions",()=>{
  const p=v("p"),pi=T.at(p,I.variable("i"));
  const functionType=T.pi("x",two,path(two,v("x"),v("x")));
  const body=T.line("i",path(two,pi,pi),app(v("f"),pi));
  const reflexivity=T.lam("x",two,T.line("i",two,v("x")));
  // Insert this closed function under an equally named outer dimension, then
  // apply it to a term using that outer dimension. Beta must rename its binder.
  const term=app(T.lam("f",functionType,body),reflexivity);
  const result=agree(term,null,[["p",path(two,left,right)]]);
  assert.equal(result.normal.tag,"PLam");
  assert.equal(result.normal.body.tag,"PLam");
  assert.notEqual(result.normal.dim,result.normal.body.dim);
  assert(I.equal(result.normal.body.body.arg,I.variable(result.normal.dim)));
});
