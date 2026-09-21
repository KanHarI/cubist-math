import test from "node:test";
import assert from "node:assert/strict";
import {Checker,T} from "../core.mjs";
import {interval as I} from "../lattice.mjs";
const v=T.variable, app=T.app, at=T.at, path=(A,x,y)=>T.path("r",A,x,y);
const a=v("a"), b=v("b"), A=v("A"), B=v("B"), f=v("f"), g=v("g");
const assumptions=[["A",T.universe(0)],["a",A],["b",A],["p",path(A,a,b)]];

test("closed Pi/Sigma/Nat computation and universe cumulativity",()=>{
  const c=new Checker();
  assert.deepEqual(c.verify(app(T.lam("n",T.nat,T.succ(v("n"))),T.zero),T.nat).normal,T.succ(T.zero));
  const pair=T.pair(T.sigma("X",T.universe(0),v("X")),T.nat,T.zero);
  assert.deepEqual(c.verify(T.second(pair),T.nat).normal,T.zero);
  c.verify(T.nat,T.universe(2));
  assert.throws(()=>c.verify(T.universe(1),T.universe(1)),/Type mismatch/);
});
test("neutral paths compute at both endpoints",()=>{
  const c=new Checker();
  assert.deepEqual(c.verify(at(v("p"),I.zero),A,assumptions).normal,a);
  assert.deepEqual(c.verify(at(v("p"),I.one),A,assumptions).normal,b);
});
test("path abstraction, reversal, beta and eta",()=>{
  const c=new Checker();
  const reverse=T.line("i",A,at(v("p"),I.reverse(I.variable("i"))));
  c.verify(reverse,path(A,b,a),assumptions);
  const double=T.line("j",A,at(reverse,I.reverse(I.variable("j"))));
  assert.deepEqual(c.verify(double,path(A,a,b),assumptions).normal,v("p"));
});
test("dependent paths specialize their family at the endpoints",()=>{
  const c=new Checker();
  const P=v("P"), q=v("q"), family=at(P,I.variable("i"));
  const context=[["P",path(T.universe(0),T.nat,T.unit)],["q",T.path("i",family,T.zero,T.point)]];
  assert.deepEqual(c.verify(at(q,I.zero),T.nat,context).normal,T.zero);
  assert.deepEqual(c.verify(at(q,I.one),T.unit,context).normal,T.point);
  c.verify(T.line("i",at(P,I.reverse(I.variable("i"))),at(q,I.reverse(I.variable("i")))),
    T.path("i",at(P,I.reverse(I.variable("i"))),T.point,T.zero),context);
});
test("function extensionality is an interval abstraction, without an axiom",()=>{
  const x=v("x"), Bx=app(B,x), functionType=T.pi("x",A,Bx);
  const pointwise=T.pi("x",A,path(Bx,app(f,x),app(g,x)));
  const context=[["A",T.universe(0)],["B",T.pi("z",A,T.universe(0))],["f",functionType],["g",functionType],["h",pointwise]];
  const funext=T.line("i",functionType,T.lam("x",A,at(app(v("h"),x),I.variable("i"))));
  const c=new Checker(), checked=c.verify(funext,path(functionType,f,g),context);
  assert.equal(checked.type.tag,"Path");
  const applyBack=T.lam("x",A,T.line("j",Bx,app(at(funext,I.variable("j")),x)));
  assert.deepEqual(c.verify(applyBack,pointwise,context).normal,v("h"));
});
test("a square's opposite reversals cancel, including connections",()=>{
  const c=new Checker();
  const sqType=path(path(A,a,b),v("p"),v("p"));
  const context=[...assumptions,["square",sqType]];
  const sq=T.line("i",path(A,a,b),T.line("j",A,
    at(at(v("square"),I.variable("i")),I.variable("j"))));
  assert.deepEqual(c.verify(sq,sqType,context).normal,v("square"));
});
test("bad endpoints, unbound dimensions and forged annotations are rejected",()=>{
  const c=new Checker();
  assert.throws(()=>c.verify(T.line("i",T.nat,T.zero),path(T.nat,T.zero,T.succ(T.zero))),/Type mismatch/);
  assert.throws(()=>c.verify(at(v("p"),I.variable("missing")),A,assumptions),/Unbound dimension/);
  const forged={...at(v("p"),I.zero),pathType:path(T.nat,T.zero,T.zero)};
  assert.deepEqual(c.verify(forged,A,assumptions).normal,a);
  assert.throws(()=>c.verify(T.variable("I")),/Unbound term/);
  assert.throws(()=>c.verify({tag:"Glue"}),/finite Glue system/);
});
test("term substitution avoids capture under binders",()=>{
  const c=new Checker();
  const term=app(T.lam("x",T.nat,T.lam("y",T.nat,v("x"))),v("y"));
  const checked=c.verify(term,T.pi("z",T.nat,T.nat),[["y",T.nat]]);
  // Source deliberately shadows a context name; elaboration alpha-renames it.
  assert.equal(checked.normal.tag,"Lam");
  assert.notEqual(checked.normal.name,"y");
  assert.deepEqual(checked.normal.body,v("y"));
});
