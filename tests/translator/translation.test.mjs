import "../fresh-build.mjs";
import createCubical from "../../web/dist/cubical.mjs";
import {CubicalProgram} from "../../web/cubical-program.mjs";
import {sourceReader} from "../../tools/module-sources.mjs";
import {numeral} from "../../web/translator/numerals.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import {Translator} from "../../web/translator/translate.mjs";
import {T} from "../../web/translator/core.mjs";
import {kernelChecker} from "./kernel-check.mjs";
import {checkTestModule} from "../check-program.mjs";
test("all four original basics declarations translate and check",async t=>{
  const source=await readFile(new URL("../../archive/first-library/basics.cubist",import.meta.url),"utf8");
  const program=new CubicalProgram(await createCubical(),sourceReader()); t.after(()=>program.dispose());
  const result=await program.check(source,"basics");
  assert.deepEqual(result.outputs.map(d=>[d.name,d.verified]),[
    ["identity",true],["duplicate",true],
    ["copy",true],["copy_of_two",true]]);
  assert.deepEqual(program.inspect("basics__copy_of_two",{normalize:true}).expression.body,numeral(2));
});
// The Cubist cases are cubist-tests/translation_*.cubist, whose comments
// state each refusal (tests/cubist-tests.test.mjs); here, what a refusal
// leaves in the kernel and the module.
test("a failed proof leaves no kernel definition, and an untranslated name",async t=>{
  const {program}=await checkTestModule(t,"translation_failed_proofs");
  assert.equal(program.kernel.definitions.has("translation_failed_proofs__wrong"),false);
  assert.equal(program.modules.get("translation_failed_proofs").get("wrong").tag,"Untranslated");
});
test("bare J and the removed word Universe remain explicit gaps",()=>{
  const result=new Translator({checker:kernelChecker()}).translate(`def schema(U : Universe, A : U) := A;
    def j := path_induction;`);
  assert(result.declarations.every(d=>d.status==="not-translated"));
  assert.match(result.declarations[0].reason,/Universe was removed: bind a universe variable as U < UU0/);
  assert.match(result.declarations[1].reason,/path_induction/);
});
