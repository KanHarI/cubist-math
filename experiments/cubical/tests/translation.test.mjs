import test from "node:test";
import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import {Translator} from "../translate.mjs";
import {T} from "../core.mjs";
test("all four original basics declarations translate and check",async()=>{
  const source=await readFile(new URL("../../../web/proofs/basics.proof",import.meta.url),"utf8");
  const result=new Translator().translate(source);
  assert.deepEqual(result.declarations.map(d=>[d.name,d.status]),[
    ["identity","checked-cubical-fragment"],["duplicate","checked-cubical-fragment"],
    ["copy","checked-cubical-fragment"],["copy_of_two","checked-cubical-fragment"]]);
  assert.deepEqual(result.declarations[3].normal.body,T.succ(T.succ(T.zero)));
});
test("failed proofs never become axioms or usable definitions",()=>{
  const result=new Translator().translate(`theorem wrong : 0 = 1 { exact refl(0); }
    def bad = wrong; def good = 0;`);
  assert.equal(result.declarations[0].status,"not-translated");
  assert.match(result.declarations[0].reason,/Type mismatch/);
  assert.equal(result.declarations[1].status,"not-translated");
  assert.equal(result.declarations[2].status,"checked-cubical-fragment");
  assert.equal(result.env.get("wrong").tag,"Untranslated");
});
test("J and universe schemas remain explicit migration gaps",()=>{
  const result=new Translator().translate(`def schema(U : Universe, A : U) = A;
    def j = path_induction;`);
  assert(result.declarations.every(d=>d.status==="not-translated"));
  assert.match(result.declarations[0].reason,/Universe/);
  assert.match(result.declarations[1].reason,/path_induction/);
});
