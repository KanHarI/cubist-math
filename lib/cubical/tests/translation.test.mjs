import test from "node:test";
import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import {Translator} from "../translate.mjs";
import {T} from "../core.mjs";
test("all four original basics declarations translate and check",async()=>{
  const source=await readFile(new URL("../../../archive/first-library/basics.cubist",import.meta.url),"utf8");
  const result=new Translator().translate(source);
  assert.deepEqual(result.declarations.map(d=>[d.name,d.status]),[
    ["identity","checked-cubical-fragment"],["duplicate","checked-cubical-fragment"],
    ["copy","checked-cubical-fragment"],["copy_of_two","checked-cubical-fragment"]]);
  assert.deepEqual(result.declarations[3].normal.body,T.succ(T.succ(T.zero)));
});
test("failed proofs never become axioms or usable definitions",()=>{
  const result=new Translator().translate(`def wrong : 0 = 1 { exact refl(0); }
    def bad = wrong; def good = 0;`);
  assert.equal(result.declarations[0].status,"not-translated");
  assert.match(result.declarations[0].reason,/Type mismatch/);
  assert.equal(result.declarations[1].status,"not-translated");
  assert.equal(result.declarations[2].status,"checked-cubical-fragment");
  assert.equal(result.env.get("wrong").tag,"Untranslated");
});
test("bare J and universe schemas remain explicit migration gaps",()=>{
  const result=new Translator().translate(`def schema(U : Universe, A : U) = A;
    def j = path_induction;`);
  assert(result.declarations.every(d=>d.status==="not-translated"));
  assert.match(result.declarations[0].reason,/Universe/);
  assert.match(result.declarations[1].reason,/path_induction/);
});
test("Path induction derives weak J from composition and singleton contraction",()=>{
  const source=`def transport_nat(A : U0, x : A, y : A, p : x = y, n : Nat) =
    path_induction(A, fun (a : A) => fun (b : A) => fun (q : a = b) => Nat,
      fun (a : A) => n, x, y, p);
    def example : transport_nat(Nat, 0, 0, refl(0), 2) = 2 { exact refl(2); }`;
  const result=new Translator().translate(source);
  assert(result.declarations.every(d=>d.status==="checked-cubical-fragment"),JSON.stringify(result.declarations));
});
test("weak Path J is not falsely given the old strict reflexivity beta rule",()=>{
  const source=`def stuck(A : U0, x : A) = path_induction(A,
    fun (a : A) => fun (b : A) => fun (q : a = b) => A, fun (a : A) => a, x, x, refl(x));
    def not_definitional(A : U0, x : A) : stuck(A, x) = x { exact refl(x); }`;
  const result=new Translator().translate(source);
  assert.equal(result.declarations[0].status,"checked-cubical-fragment");
  assert.equal(result.declarations[1].status,"not-translated");
  assert.match(result.declarations[1].reason,/Type mismatch/);
});
test("universe schemas instantiate at U0 and U2 without resizing",()=>{
  const result=new Translator().translate(`def id(U : Universe, A : U, x : A) = x;
    def small = id(U0, Nat, 0); def large = id(U2, U1, Nat);
    def resize = id(U0, U1, Nat);`);
  assert.equal(result.declarations[0].status,"not-translated");
  assert.equal(result.declarations[1].status,"checked-cubical-fragment");
  assert.equal(result.declarations[2].status,"checked-cubical-fragment");
  assert.equal(result.declarations[3].status,"not-translated");
});
