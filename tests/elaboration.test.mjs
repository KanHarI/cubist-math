import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { elaboration } from "../web/cubical-elaboration.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";

const readLibrary = name => readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8");
const source = `import naturals;

def lt(n, m : Nat) : U0 {
  exact exists k : Nat. succ(k) + n = m;
}

def lt_succ(n : Nat) : lt(n, succ(n)) {
  exact (0, refl(succ(n)));
}

def exists_greater_number : forall n : Nat. exists m : Nat. lt(n, m) {
  intro n;
  exact (succ(n), lt_succ(n));
}
`;

test("each proof statement reports its goal, the names in scope and the term it built", async t => {
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  const result = await program.check(source, "first");
  const steps = result.steps.map(step => [source.slice(step.start, step.end), step.locals.map(local => `${local.name} : ${local.type}`).join(", "), step.goal, step.built]);
  assert.deepEqual(steps, [
    ["exact exists k : Nat. succ(k) + n = m;", "n : Nat, m : Nat", "U0", "exists k : Nat. succ(k) + n = m"],
    ["exact (0, refl(succ(n)));", "n : Nat", "lt(n, succ(n))", "(0, refl(succ(n)))"],
    // The rest of the block's proof is a hole: intro builds only the function.
    ["intro n;", "", "forall n : Nat. exists m : Nat. lt(n, m)", "fun (n : Nat) => ?"],
    ["exact (succ(n), lt_succ(n));", "n : Nat", "exists m : Nat. lt(n, m)", "(succ(n), lt_succ(n))"],
  ]);
});

test("the elaboration view shows each declaration's type, term and the kernel's derivation", async t => {
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  await program.check(source, "first");
  const view = elaboration(program, "first");
  assert.deepEqual(view.map(declaration => [declaration.name, declaration.type, declaration.term]), [
    ["lt", "Nat -> Nat -> U0", "fun (n, m : Nat) => exists k : Nat. succ(k) + n = m"],
    ["lt_succ", "forall n : Nat. lt(n, succ(n))", "fun (n : Nat) => (0, refl(succ(n)))"],
    ["exists_greater_number", "forall n : Nat. exists m : Nat. lt(n, m)", "fun (n : Nat) => (succ(n), lt_succ(n))"],
  ]);
  const derivation = declaration => declaration.derivation.steps.map(step =>
    `${step.number} ${step.rule}(${step.premises.join(", ")})${step.note ? ` ${step.note}` : ""} // ${step.comment}${step.scaffold ? " [elaborator]" : ""}`);
  assert.ok(view.every(declaration => declaration.derivation.source === "instructions"));
  const ltSucc = derivation(view[1]);
  // The instruction kernel's derivation, in the style of THTH: rules on earlier steps.
  assert.deepEqual(ltSucc.slice(0, 7), [
    "1 NatForm() // {} ⊢ Nat : U0",
    "2 DefLookup() // {} ⊢ lt : (Nat → (Nat → U0))",
    "3 CtxExt(1) // {n : Nat}",
    "4 Vble(3) // {n : Nat} ⊢ n : Nat",
    "5 PiElim(2, 4) // {n : Nat} ⊢ lt(n) : (Nat → U0)",
    "6 NatIntroS(4) // {n : Nat} ⊢ succ(n) : Nat",
    "7 PiElim(5, 6) // {n : Nat} ⊢ lt(n, succ(n)) : U0",
  ]);
  // The goal is unfolded at its highlighted head: lt, at [0, 0] of the other side.
  assert.ok(ltSucc.some(step => /^\d+ Delta\(\d+\) at the other \[0, 0\]: lt \/\/ \{n : Nat\} ⊢ lt\(n, succ\(n\)\) ≡ /.test(step)));
  // refl(succ(n)) proves succ(0) + n = succ(n) by computing the addition.
  assert.ok(ltSucc.some(step => /^\d+ Iota\(\d+\) at the other \[1, 0\]: NatRec\(/.test(step)));
  assert.ok(ltSucc.some(step => /^\d+ Conv\(\d+, \d+\) \/\/ \{n : Nat\} ⊢ refl\(succ\(n\)\) : \(add\(1, n\) =\[/.test(step)));
  assert.ok(ltSucc.some(step => /^\d+ SigmaIntro\(\d+, \d+, \d+\) \/\/ \{n : Nat\} ⊢ \(0 , refl\(succ\(n\)\)\) : Σ \(k : Nat\)/.test(step)));
  assert.ok(ltSucc.some(step => /^\d+ Conv\(\d+, \d+\) \/\/ \{n : Nat\} ⊢ \(0 , refl\(succ\(n\)\)\) : lt\(n, succ\(n\)\)$/.test(step)));
  // exact's ascription is the elaborator's, and marked; the proof is not.
  assert.ok(ltSucc.some(step => /PiIntro.*λ \(ascription : lt\(n, succ\(n\)\)\)\. ascription.*\[elaborator\]$/.test(step)));
  assert.ok(ltSucc.includes("8 CtxExt(7) // {n : Nat, ascription : lt(n, succ(n))} [elaborator]"));
  assert.ok(!ltSucc.some(step => /SigmaIntro.*\[elaborator\]/.test(step)));
  // Every premise is an earlier step.
  for (const declaration of view) for (const step of declaration.derivation.steps)
    assert.ok(step.premises.every(premise => premise < step.number));
  assert.ok(view.every(declaration => !declaration.derivation.truncated));
  // Tracing turns check reuse off only while it runs.
  assert.equal(program.kernel.optimizations?.reuseChecks ?? true, true);
});

test("a declaration outside instruction mode shows the kernel's traced check instead", async t => {
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  await program.check("def Suspension(A : U0) := Pushout(A, Unit, Unit, fun (a : A) => tt, fun (a : A) => tt);\n", "suspension");
  // Whatever the driver cannot derive yet; here, it is made to fail.
  const check = InstructionDriver.prototype.check;
  InstructionDriver.prototype.check = () => { throw new Error("Pushout is not in instruction mode yet."); };
  let suspension;
  try { [suspension] = elaboration(program, "suspension"); }
  finally { InstructionDriver.prototype.check = check; }
  assert.equal(suspension.derivation.source, "trace");
  assert.match(suspension.derivation.reason, /Pushout is not in instruction mode yet/);
  assert.ok(suspension.derivation.steps.length > 0);
  // In instruction mode, the same declaration's derivation is the driver's.
  const [derived] = elaboration(program, "suspension");
  assert.notEqual(derived.derivation.source, "trace");
});
