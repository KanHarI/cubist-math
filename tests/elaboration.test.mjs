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

test("the elaboration view shows each declaration's term and type as native opcode trees", async t => {
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  await program.check(source, "first");
  const view = elaboration(program, "first");
  assert.deepEqual(view.map(declaration => [declaration.name, declaration.type, declaration.term]), [
    ["lt", "Nat -> Nat -> U0", "fun (n, m : Nat) => exists k : Nat. succ(k) + n = m"],
    ["lt_succ", "forall n : Nat. lt(n, succ(n))", "fun (n : Nat) => (0, refl(succ(n)))"],
    ["exists_greater_number", "forall n : Nat. exists m : Nat. lt(n, m)", "fun (n : Nat) => (succ(n), lt_succ(n))"],
  ]);
  const tree = lines => lines.map(line => `${"  ".repeat(line.depth)}${line.text}`);
  assert.deepEqual(tree(view[0].kernelType), ["CC_PI n : CC_NAT", "  CC_PI m : CC_NAT", "    CC_U 0"]);
  assert.deepEqual(tree(view[0].kernelTerm).slice(0, 2), ["CC_LAM n : CC_NAT", "  CC_LAM m : CC_NAT"]);
  // exact checks its value at the goal through an ascription.
  assert.ok(tree(view[0].kernelTerm).some(line => /CC_LAM ascription : CC_U 0/.test(line)));
  assert.ok(tree(view[2].kernelTerm).some(line => /second: CC_APP \(CC_DEFREF lt_succ\) \(CC_VAR n\)/.test(line)));
});

test("the kernel's check is shown rule by rule, from the kernel's own trace", async t => {
  const program = new CubicalProgram(await createCubical(), readLibrary);
  t.after(() => program.dispose());
  await program.check(source, "first");
  const [lt, ltSucc] = elaboration(program, "first");
  const lines = derivation => derivation.lines.map(line => `${"  ".repeat(line.depth)}${line.kind} ${line.text}${line.result ? ` ⇒ ${line.result}` : ""}`);
  const shown = lines(lt.derivation);
  // Entering a binder: the domain is checked, then the context gains n : Nat.
  assert.deepEqual(shown.slice(0, 3), ["infer CC_LAM n : CC_NAT ⇒ Nat -> Nat -> U0", "  infer CC_NAT ⇒ U0", "  extend n : Nat"]);
  // The inferred type is compared with the declared one.
  assert.equal(shown.at(-1), "convert Nat -> Nat -> U0 ≡ Nat -> Nat -> U0 ⇒ equal");
  // lt unfolds when its value is checked as a pair.
  assert.ok(lines(ltSucc.derivation).some(line => /reduce lt\(n, succ\(n\)\) ⟶ exists k : Nat\. succ\(k\) \+ n = succ\(n\)/.test(line)));
  assert.ok(lt.derivation.rulesApplied > 20 && !lt.derivation.truncated);
  // Tracing turns check reuse off only while it runs.
  assert.equal(program.kernel.optimizations?.reuseChecks ?? true, true);
});
