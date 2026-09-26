import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { elaboration } from "../web/cubical-elaboration.mjs";

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
    `${step.number} ${step.rule}(${step.premises.join(", ")}) // ${step.comment}${step.scaffold ? " [elaborator]" : ""}`);
  const ltSucc = derivation(view[1]);
  // A forward derivation in the style of THTH: rules on earlier steps.
  assert.deepEqual(ltSucc.slice(0, 7), [
    "1 NatForm() // {} ⊢ Nat : U0",
    "2 CtxExt(1) // {n : Nat}",
    "3 DefLookup() // {} ⊢ lt : (Nat → (Nat → U0))",
    "4 Vble(2) // {n : Nat} ⊢ n : Nat",
    "5 PiElim(3, 4) // {n : Nat} ⊢ lt(n) : (Nat → U0)",
    "6 NatIntroS(4) // {n : Nat} ⊢ succ(n) : Nat",
    "7 PiElim(5, 6) // {n : Nat} ⊢ lt(n, succ(n)) : U0",
  ]);
  // refl(succ(n)) proves succ(0) + n = succ(n) by conversion.
  assert.ok(ltSucc.includes("13 Conv(12) // {n : Nat} ⊢ (succ(n) =[Nat] succ(n)) ≡ (add(1, n) =[Nat] succ(n))"));
  assert.ok(ltSucc.some(step => /^\d+ SigmaIntro\(7, 11, 12, 13\) \/\/ \{n : Nat\} ⊢ \(0 , refl\(succ\(n\)\)\) : lt\(n, succ\(n\)\)$/.test(step)));
  // exact's ascription is the elaborator's, and marked; the proof is not.
  assert.ok(ltSucc.some(step => /PiIntro.*λ \(ascription : lt\(n, succ\(n\)\)\)\. ascription.*\[elaborator\]$/.test(step)));
  assert.ok(!ltSucc.some(step => /SigmaIntro.*\[elaborator\]/.test(step)));
  assert.ok(view.every(declaration => !declaration.derivation.truncated));
  // Tracing turns check reuse off only while it runs.
  assert.equal(program.kernel.optimizations?.reuseChecks ?? true, true);
});
