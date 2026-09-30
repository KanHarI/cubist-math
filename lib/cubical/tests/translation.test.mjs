import "../../../tests/fresh-build.mjs";
import createCubical from "../../../web/dist/cubical.mjs";
import {CubicalProgram} from "../../../web/cubical-program.mjs";
import {sourceReader} from "../../../tools/module-sources.mjs";
import {numeral} from "../numerals.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import {Translator} from "../translate.mjs";
import {T} from "../core.mjs";
test("all four original basics declarations translate and check",async t=>{
  const source=await readFile(new URL("../../../archive/first-library/basics.cubist",import.meta.url),"utf8");
  const program=new CubicalProgram(await createCubical(),sourceReader()); t.after(()=>program.dispose());
  const result=await program.check(source,"basics");
  assert.deepEqual(result.outputs.map(d=>[d.name,d.verified]),[
    ["identity",true],["duplicate",true],
    ["copy",true],["copy_of_two",true]]);
  assert.deepEqual(program.inspect("basics__copy_of_two",{normalize:true}).expression.body,numeral(2));
});
test("failed proofs never become axioms or usable definitions",async t=>{
  const program=new CubicalProgram(await createCubical(),sourceReader()); t.after(()=>program.dispose());
  const result=await program.check(`def wrong : 0 = 1 { exact refl(0); }
    def bad := wrong; def good := 0;`,"main");
  assert.equal(result.outputs[0].verified,false);
  assert.match(result.outputs[0].reason,/Type mismatch/);
  assert.equal(program.kernel.definitions.has("main__wrong"),false);
  assert.equal(result.outputs[1].verified,false);
  assert.equal(result.outputs[2].verified,true);
  assert.equal(program.modules.get("main").get("wrong").tag,"Untranslated");
});
test("bare J and the removed word Universe remain explicit gaps",()=>{
  const result=new Translator().translate(`def schema(U : Universe, A : U) := A;
    def j := path_induction;`);
  assert(result.declarations.every(d=>d.status==="not-translated"));
  assert.match(result.declarations[0].reason,/Universe was removed: bind a universe variable as U < UU0/);
  assert.match(result.declarations[1].reason,/path_induction/);
});
test("Path induction derives weak J from composition and singleton contraction",async t=>{
  const source=`def transport_nat(A : U0, x : A, y : A, p : x = y, n : Nat) :=
    path_induction(A, fun (a : A) => fun (b : A) => fun (q : a = b) => Nat,
      fun (a : A) => n, x, y, p);
    def example : transport_nat(Nat, 0, 0, refl(0), 2) = 2 { exact refl(2); }`;
  const program=new CubicalProgram(await createCubical(),sourceReader()); t.after(()=>program.dispose());
  const result=await program.check(source,"main");
  assert(result.complete,JSON.stringify(result.gaps));
});
test("weak Path J is not falsely given the old strict reflexivity beta rule",()=>{
  const source=`def stuck(A : U0, x : A) := path_induction(A,
    fun (a : A) => fun (b : A) => fun (q : a = b) => A, fun (a : A) => a, x, x, refl(x));
    def not_definitional(A : U0, x : A) : stuck(A, x) = x { exact refl(x); }`;
  const result=new Translator().translate(source);
  assert.equal(result.declarations[0].status,"checked-cubical-fragment");
  assert.equal(result.declarations[1].status,"not-translated");
  assert.match(result.declarations[1].reason,/Type mismatch/);
});
// G0: universe-generic declarations are checked by the native kernel
// (tests/universe-generic.test.mjs). The reference checker has no level
// rules and says so; declarations at fixed universes still check here.
test("the reference checker declines universe-generic declarations by name",()=>{
  const result=new Translator().translate(`def id(U < UU0, A : U, x : A) := x;
    def small := id(U0, Nat, 0); def fixed(A : U2) := A;`);
  assert.deepEqual(result.declarations.map(d=>d.status),["not-translated","not-translated","checked-cubical-fragment"]);
  assert.match(result.declarations[0].reason,/reference checker has no rules for universe levels/);
  assert.match(result.declarations[1].reason,/Untranslated dependency: id/);
});
