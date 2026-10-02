import "../../../tests/fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {T,substituteTerm} from "../core.mjs";
import {interval as I} from "../lattice.mjs";
import {checkKernel} from "./kernel-check.mjs";
// The kernel's check, with a refusal as an exception.
const kernel={verify(term,type=null,ctx=[]){const result=checkKernel(term,type,ctx);if(!result.ok)throw Error(result.error);return result;}};
// Two points, the examples' small inductive type.
const two=T.sum(T.unit,T.unit),left=T.inl(two,T.point),right=T.inr(two,T.point);
const v=T.variable, app=T.app, at=T.at, path=(A,x,y)=>T.path("r",A,x,y);
const a=v("a"), b=v("b"), A=v("A"), B=v("B"), f=v("f"), g=v("g");
const assumptions=[["A",T.universe(0)],["a",A],["b",A],["p",path(A,a,b)]];

test("closed Pi/Sigma/Sum computation and universe cumulativity",()=>{
  const c=kernel,swap=T.lam("n",two,T.sumrec(T.lam("_",two,two),T.lam("u",T.unit,right),T.lam("u",T.unit,left),v("n")));
  assert.deepEqual(c.verify(app(swap,left),two).normal,right);
  const pair=T.pair(T.sigma("X",T.universe(0),v("X")),two,left);
  assert.deepEqual(c.verify(T.second(pair),two).normal,left);
  c.verify(two,T.universe(2));
  assert.throws(()=>c.verify(T.universe(1),T.universe(1)),/Type mismatch/);
});
test("neutral paths compute at both endpoints",()=>{
  const c=kernel;
  assert.deepEqual(c.verify(at(v("p"),I.zero),A,assumptions).normal,a);
  assert.deepEqual(c.verify(at(v("p"),I.one),A,assumptions).normal,b);
});
test("path abstraction, reversal, beta and eta",()=>{
  const c=kernel;
  const reverse=T.line("i",A,at(v("p"),I.reverse(I.variable("i"))));
  c.verify(reverse,path(A,b,a),assumptions);
  const double=T.line("j",A,at(reverse,I.reverse(I.variable("j"))));
  assert.deepEqual(c.verify(double,path(A,a,b),assumptions).normal,v("p"));
});
test("dependent paths specialize their family at the endpoints",()=>{
  const c=kernel;
  const P=v("P"), q=v("q"), family=at(P,I.variable("i"));
  const context=[["P",path(T.universe(0),two,T.unit)],["q",T.path("i",family,left,T.point)]];
  assert.deepEqual(c.verify(at(q,I.zero),two,context).normal,left);
  assert.deepEqual(c.verify(at(q,I.one),T.unit,context).normal,T.point);
  c.verify(T.line("i",at(P,I.reverse(I.variable("i"))),at(q,I.reverse(I.variable("i")))),
    T.path("i",at(P,I.reverse(I.variable("i"))),T.point,left),context);
});
test("function extensionality is an interval abstraction, without an axiom",()=>{
  const x=v("x"), Bx=app(B,x), functionType=T.pi("x",A,Bx);
  const pointwise=T.pi("x",A,path(Bx,app(f,x),app(g,x)));
  const context=[["A",T.universe(0)],["B",T.pi("z",A,T.universe(0))],["f",functionType],["g",functionType],["h",pointwise]];
  const funext=T.line("i",functionType,T.lam("x",A,at(app(v("h"),x),I.variable("i"))));
  const c=kernel, checked=c.verify(funext,path(functionType,f,g),context);
  assert.equal(checked.type.tag,"Path");
  const applyBack=T.lam("x",A,T.line("j",Bx,app(at(funext,I.variable("j")),x)));
  assert.deepEqual(c.verify(applyBack,pointwise,context).normal,v("h"));
});
test("a square's opposite reversals cancel, including connections",()=>{
  const c=kernel;
  const sqType=path(path(A,a,b),v("p"),v("p"));
  const context=[...assumptions,["square",sqType]];
  const sq=T.line("i",path(A,a,b),T.line("j",A,
    at(at(v("square"),I.variable("i")),I.variable("j"))));
  assert.deepEqual(c.verify(sq,sqType,context).normal,v("square"));
});
test("bad endpoints, unbound dimensions and forged annotations are rejected",()=>{
  const c=kernel;
  assert.throws(()=>c.verify(T.line("i",two,left),path(two,left,right)),/mismatch/i);
  assert.throws(()=>c.verify(at(v("p"),I.variable("missing")),A,assumptions),/Unbound cubical dimension/);
  // A path application's annotation is not read: the endpoint is the path's own.
  const forged={...at(v("p"),I.zero),pathType:path(two,left,left)};
  assert.deepEqual(c.verify(forged,A,assumptions).normal,a);
  assert.throws(()=>c.verify(T.variable("I")),/unbound/i);
});
test("term substitution avoids capture under binders",()=>{
  const c=kernel;
  const term=app(T.lam("x",two,T.lam("y",two,v("x"))),v("y"));
  const checked=c.verify(term,T.pi("z",two,two),[["y",two]]);
  // Source deliberately shadows a context name; elaboration alpha-renames it.
  assert.equal(checked.normal.tag,"Lam");
  assert.notEqual(checked.normal.name,"y");
  assert.deepEqual(checked.normal.body,v("y"));
});
test("shared syntax substituted below different binders keeps each scope",()=>{
  const shared=app(v("target"),v("z"));
  const term=app(T.lam("y",two,shared),T.lam("z",two,shared));
  const changed=substituteTerm(term,"target",v("y"));
  assert.notEqual(changed.fn.name,"y");
  assert.equal(changed.arg.name,"z");
  assert.equal(changed.fn.body.fn.name,"y");
  assert.equal(changed.arg.body.fn.name,"y");
});
