import test from "node:test";
import assert from "node:assert/strict";
import {spawnSync} from "node:child_process";
import {fileURLToPath} from "node:url";
import {Checker,T} from "../core.mjs";
import {interval as I} from "../lattice.mjs";
import {checkNative,nativeRequest} from "../native.mjs";
const root=fileURLToPath(new URL("../../../kernel/",import.meta.url));
const build=spawnSync("make",["-C",root,"all"],{encoding:"utf8"});assert.equal(build.status,0,build.stderr);
const v=T.variable,app=T.app,path=(A,a,b)=>T.path("i",A,a,b);
function agree(term,type=null,ctx=[]){
  const js=new Checker(),expected=js.verify(term,type,ctx),native=checkNative(term,type,ctx);
  assert(native.ok,native.error);
  assert(js.equal(native.type,expected.type),JSON.stringify({native:native.type,expected:expected.type}));
  assert(js.equal(native.normal,expected.normal),JSON.stringify({native:native.normal,expected:expected.normal}));
  js.verify(native.normal,expected.type,ctx);
  return native;
}
test("native dependent Pi/Sigma checking and reduction agree with reference",()=>{
  agree(app(T.lam("n",T.nat,T.succ(v("n"))),T.zero),T.nat);
  const sigma=T.sigma("A",T.universe(0),v("A"));
  agree(T.second(T.pair(sigma,T.nat,T.zero)),T.nat);
  agree(T.nat,T.universe(2));
  assert.equal(checkNative(T.universe(1),T.universe(1)).ok,false);
});
test("native path endpoints, reversal and dependent families agree",()=>{
  const A=v("A"),a=v("a"),b=v("b"),p=v("p"),ctx=[["A",T.universe(0)],["a",A],["b",A],["p",path(A,a,b)]];
  agree(T.at(p,I.zero),A,ctx);agree(T.at(p,I.one),A,ctx);
  agree(T.line("j",A,T.at(p,I.reverse(I.variable("j")))),path(A,b,a),ctx);
  const P=v("P"),q=v("q"),dep=[["P",path(T.universe(0),T.nat,T.unit)],["q",T.path("j",T.at(P,I.variable("j")),T.zero,T.point)]];
  agree(T.at(q,I.one),T.unit,dep);
});
test("native computational dependent FunExt uses no axiom",()=>{
  const A=v("A"),B=v("B"),x=v("x"),f=v("f"),g=v("g"),Bx=app(B,x),ft=T.pi("x",A,Bx);
  const ht=T.pi("x",A,path(Bx,app(f,x),app(g,x)));
  const ctx=[["A",T.universe(0)],["B",T.pi("z",A,T.universe(0))],["f",ft],["g",ft],["h",ht]];
  agree(T.line("j",ft,T.lam("x",A,T.at(app(v("h"),x),I.variable("j")))),path(ft,f,g),ctx);
});
test("native Nat induction computes and rejects a wrong recursive step",()=>{
  const motive=T.lam("n",T.nat,T.nat),step=T.lam("n",T.nat,T.lam("ih",T.nat,T.succ(v("ih"))));
  agree(T.natrec(motive,T.zero,step,T.succ(T.succ(T.zero))),T.nat);
  const wrong=T.lam("n",T.nat,T.lam("ih",T.unit,T.zero));
  assert.equal(checkNative(T.natrec(motive,T.zero,wrong,T.zero)).ok,false);
});
test("native checker rejects forged endpoint claims and unbound variables",()=>{
  assert.equal(checkNative(T.line("j",T.nat,T.zero),path(T.nat,T.zero,T.succ(T.zero))).ok,false);
  agree(T.comp("i",T.nat,[],T.zero),T.nat);
  assert.equal(checkNative(v("missing")).ok,false);
});

test("native dependent Sum, Unit and Void rules agree",()=>{
  const two=T.sum(T.unit,T.unit),l=T.inl(two,T.point),r=T.inr(two,T.point);
  const family=T.lam("tag",two,T.sumrec(T.lam("_",two,T.universe(0)),T.lam("_",T.unit,T.nat),T.lam("_",T.unit,T.unit),v("tag")));
  agree(T.sumrec(family,T.lam("u",T.unit,T.zero),T.lam("u",T.unit,T.point),l),T.nat);
  agree(T.sumrec(family,T.lam("u",T.unit,T.zero),T.lam("u",T.unit,T.point),r),T.unit);
  agree(T.unitrec(T.lam("u",T.unit,path(T.unit,v("u"),v("u"))),T.line("i",T.unit,T.point),T.point));
  agree(T.abort(T.nat,v("impossible")),T.nat,[["impossible",T.void]]);
  assert.equal(checkNative(T.abort(T.nat,T.point)).ok,false);
  assert.equal(checkNative(T.sumrec(family,T.lam("u",T.unit,T.point),T.lam("u",T.unit,T.point),l)).ok,false);
});

test("native general W induction retains dependent motives and child hypotheses",()=>{
  const W=T.w("label",T.unit,T.void),noChildren=T.lam("none",T.void,T.abort(W,v("none")));
  const leaf=T.sup(W,T.point,noChildren),children=T.pi("none",T.void,W);
  const motive=T.lam("tree",W,path(W,v("tree"),v("tree")));
  const ih=T.pi("index",T.void,app(motive,app(v("children"),v("index"))));
  const step=T.lam("label",T.unit,T.lam("children",children,T.lam("ih",ih,T.line("i",W,T.sup(W,v("label"),v("children"))))));
  agree(W,T.universe(0));
  agree(leaf,W);
  agree(T.wrec(motive,step,leaf),path(W,leaf,leaf));
  const badStep=T.lam("label",T.unit,T.lam("children",children,T.lam("ih",T.unit,T.zero)));
  assert.equal(checkNative(T.wrec(T.lam("tree",W,T.nat),badStep,leaf)).ok,false);
});

test("checking keeps exponentially large Nat computations compact",()=>{
  const natMotive=T.lam("n",T.nat,T.nat);
  const twice=T.lam("n",T.nat,T.natrec(natMotive,T.zero,T.lam("p",T.nat,T.lam("ih",T.nat,T.succ(T.succ(v("ih"))))),v("n")));
  let large=T.succ(T.zero);
  for(let i=0;i<22;i++)large=app(twice,large);
  const compact=checkNative(large,T.nat,[],{normalize:false});
  assert(compact.ok,compact.error);
  assert(compact.arenaNodes<20000,JSON.stringify(compact));
  assert(compact.arenaBytes<2*1024*1024);
  const ignored=checkNative(app(T.lam("unused",T.nat,T.zero),large),T.nat);
  assert(ignored.ok,ignored.error);
  assert.deepEqual(ignored.normal,T.zero);
});

test("native serialization keeps a shared application graph compact",()=>{
  const f=v("f");
  let term=v("n");
  for(let i=0;i<28;i++)term=app(app(f,term),term);
  const lines=nativeRequest(term).input.trim().split("\n");
  assert.ok(lines.length<100,`serialized ${lines.length} lines`);
});

test("native request and response preserve a shared graph through checking",()=>{
  const f=v("f"),context=[["f",T.pi("x",T.nat,T.pi("y",T.nat,T.nat))],["n",T.nat]];
  let term=v("n");
  for(let i=0;i<22;i++)term=app(app(f,term),term);
  const request=nativeRequest(term,T.nat,context,{normalize:false});
  assert.ok(request.input.length<1000);
  const result=checkNative(term,T.nat,context,{normalize:false});
  assert.equal(result.ok,true,result.error);
  assert.equal(result.normal.fn.arg,result.normal.arg);
  assert.deepEqual(result.type,T.nat);
});

test("native serialization reuses equivalent dimension environments",()=>{
  let type=T.nat,value=T.zero;
  for(let i=0;i<18;i++) {
    const oldType=type,oldValue=value;
    value=T.line("i",oldType,oldValue);
    type=T.path("i",oldType,oldValue,oldValue);
  }
  const request=nativeRequest(value,type,[],{normalize:false});
  assert.ok(request.input.length<2000,`serialized ${request.input.length} bytes`);
  const result=checkNative(value,type,[],{normalize:false});
  assert.equal(result.ok,true,result.error);
  assert.equal(result.normal.tag,"PLam");
});

test("native W recursive hypotheses compute through dependent sum-selected arities",()=>{
  const labels=T.sum(T.unit,T.unit),left=T.inl(labels,T.point),right=T.inr(labels,T.point);
  const arity=label=>T.sumrec(T.lam("label",labels,T.universe(0)),T.lam("u",T.unit,T.void),T.lam("u",T.unit,T.unit),label);
  const W=T.w("label",labels,arity(v("label")));
  const leaf=T.sup(W,left,T.lam("none",T.void,T.abort(W,v("none"))));
  const node=child=>T.sup(W,right,T.lam("u",T.unit,child));
  const stepFamily=T.lam("label",labels,T.pi("children",T.pi("index",arity(v("label")),W),T.pi("ih",T.pi("index",arity(v("label")),T.nat),T.nat)));
  const leafStep=T.lam("u",T.unit,T.lam("children",T.pi("none",T.void,W),T.lam("ih",T.pi("none",T.void,T.nat),T.zero)));
  const nodeStep=T.lam("u",T.unit,T.lam("children",T.pi("index",T.unit,W),T.lam("ih",T.pi("index",T.unit,T.nat),T.succ(app(v("ih"),T.point)))));
  const step=T.lam("label",labels,T.sumrec(stepFamily,leafStep,nodeStep,v("label")));
  const result=agree(T.wrec(T.lam("tree",W,T.nat),step,node(node(leaf))),T.nat);
  assert.deepEqual(result.normal,T.succ(T.succ(T.zero)));
});

test("term substitution also avoids capture of free dimensions",()=>{
  const p=v("p"),pi=T.at(p,I.variable("i"));
  const functionType=T.pi("x",T.nat,path(T.nat,v("x"),v("x")));
  const body=T.line("i",path(T.nat,pi,pi),app(v("f"),pi));
  const reflexivity=T.lam("x",T.nat,T.line("i",T.nat,v("x")));
  // Insert this closed function under an equally named outer dimension, then
  // apply it to a term using that outer dimension. Beta must rename its binder.
  const term=app(T.lam("f",functionType,body),reflexivity);
  const result=agree(term,null,[["p",path(T.nat,T.zero,T.succ(T.zero))]]);
  assert.equal(result.normal.tag,"PLam");
  assert.equal(result.normal.body.tag,"PLam");
  assert.notEqual(result.normal.dim,result.normal.body.dim);
  assert(I.equal(result.normal.body.body.arg,I.variable(result.normal.dim)));
});
