import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { elaboration } from "../web/cubical-elaboration.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { checkTestModule } from "./check-program.mjs";

const readLibrary = name => readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8");
// The first proof is cubist-tests/driver_first_proof.cubist, which the
// instruction driver's tests derive too.
const firstProof = t => checkTestModule(t, "driver_first_proof");

test("each proof statement reports its goal, the names in scope and the term it built", async t => {
  const { source, result } = await firstProof(t);
  const steps = result.steps.map(step => [source.slice(step.start, step.end), step.locals.map(local => `${local.name} : ${local.type}`).join(", "), step.goal, step.built]);
  assert.deepEqual(steps, [
    ["exact exists k : UNat. succ(k) + n = m;", "n : UNat, m : UNat", "U0", "exists k : UNat. succ(k) + n = m"],
    ["exact (0, refl(succ(n)));", "n : UNat", "lt(n, succ(n))", "(0, refl(succ(n)))"],
    // The rest of the block's proof is a hole: intro builds only the function.
    ["intro n;", "", "forall n : UNat. exists m : UNat. lt(n, m)", "fun (n : UNat) => ?"],
    ["exact (succ(n), lt_succ(n));", "n : UNat", "exists m : UNat. lt(n, m)", "(succ(n), lt_succ(n))"],
  ]);
});

test("the elaboration view shows each declaration's type, term and the kernel's derivation", async t => {
  const { program } = await firstProof(t);
  const view = elaboration(program, "driver_first_proof");
  assert.deepEqual(view.map(declaration => [declaration.name, declaration.type, declaration.term]), [
    ["lt", "UNat -> UNat -> U0", "fun (n, m : UNat) => exists k : UNat. succ(k) + n = m"],
    ["lt_succ", "forall n : UNat. lt(n, succ(n))", "fun (n : UNat) => (0, refl(succ(n)))"],
    ["exists_greater_number", "forall n : UNat. exists m : UNat. lt(n, m)", "fun (n : UNat) => (succ(n), lt_succ(n))"],
  ]);
  const derivation = declaration => declaration.derivation.steps.map(step =>
    `${step.number} ${step.rule}(${step.premises.join(", ")})${step.note ? ` ${step.note}` : ""} // ${step.comment}${step.scaffold ? " [elaborator]" : ""}`);
  assert.ok(view.every(declaration => declaration.derivation.source === "instructions"));
  const ltSucc = derivation(view[1]);
  // The instruction kernel's derivation, in the style of THTH: rules on earlier steps.
  assert.deepEqual(ltSucc.slice(0, 7), [
    "1 SortBegin() // {} ⊢ UNat : U0",
    "2 ConIntro(1) // {} ⊢ succ : (UNat → UNat)",
    "3 DefLookup() // {} ⊢ lt : (UNat → (UNat → U0))",
    "4 CtxExt(1) // {n : UNat}",
    "5 Vble(4) // {n : UNat} ⊢ n : UNat",
    "6 PiElim(3, 5) // {n : UNat} ⊢ lt(n) : (UNat → U0)",
    "7 PiElim(2, 5) // {n : UNat} ⊢ succ(n) : UNat",
  ]);
  // The goal is unfolded at its highlighted head: lt, at [0, 0] of the other side.
  assert.ok(ltSucc.some(step => /^\d+ Delta\(\d+\) at the other \[0, 0\]: lt \/\/ \{n : UNat\} ⊢ lt\(n, succ\(n\)\) ≡ /.test(step)));
  // refl(succ(n)) proves succ(0) + n = succ(n) by computing the addition.
  assert.ok(ltSucc.some(step => /^\d+ Iota\(\d+\) at the other \[1, 0, 1\]: UNat\.elim\(/.test(step)));
  assert.ok(ltSucc.some(step => /^\d+ Conv\(\d+, \d+\) \/\/ \{n : UNat\} ⊢ refl\(succ\(n\)\) : \(add\(1, n\) =\[/.test(step)));
  assert.ok(ltSucc.some(step => /^\d+ SigmaIntro\(\d+, \d+, \d+\) \/\/ \{n : UNat\} ⊢ \(0 , refl\(succ\(n\)\)\) : Σ \(k : UNat\)/.test(step)));
  assert.ok(ltSucc.some(step => /^\d+ Conv\(\d+, \d+\) \/\/ \{n : UNat\} ⊢ \(0 , refl\(succ\(n\)\)\) : lt\(n, succ\(n\)\)$/.test(step)));
  // exact's ascription is the elaborator's, and marked; the proof is not.
  assert.ok(ltSucc.some(step => /PiIntro.*λ \(ascription : lt\(n, succ\(n\)\)\)\. ascription.*\[elaborator\]$/.test(step)));
  assert.ok(ltSucc.includes("9 CtxExt(8) // {n : UNat, ascription : lt(n, succ(n))} [elaborator]"));
  assert.ok(!ltSucc.some(step => /SigmaIntro.*\[elaborator\]/.test(step)));
  // Every premise is an earlier step.
  for (const declaration of view) for (const step of declaration.derivation.steps)
    assert.ok(step.premises.every(premise => premise < step.number));
  assert.ok(view.every(declaration => !declaration.derivation.truncated));
  // Tracing turns check reuse off only while it runs.
  assert.equal(program.kernel.optimizations?.reuseChecks ?? true, true);
});

test("a declaration the instruction kernel cannot derive shows why, not a derivation", async t => {
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  await program.check("def Doubled(A : U0) : U0 := A or A;\n", "suspension");
  // Whatever the driver cannot derive; here, it is made to fail.
  const check = InstructionDriver.prototype.check;
  InstructionDriver.prototype.check = () => { throw new Error("The search could not derive this."); };
  let suspension;
  try { [suspension] = elaboration(program, "suspension"); }
  finally { InstructionDriver.prototype.check = check; }
  // There is no other derivation to show: the term checker no longer checks,
  // and the declaration's view is itself derived.
  assert.equal(suspension.derivation, undefined);
  assert.match(suspension.reason, /^Instruction kernel: The search could not derive this/);
  const [derived] = elaboration(program, "suspension");
  assert.ok(derived.derivation.steps.length > 0);
  assert.equal(derived.derivation.reason, undefined);
});
