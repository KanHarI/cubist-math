import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { parse } from "../web/mathscript/parser.mjs";
import { formatMathScript } from "../web/mathscript/formatter.mjs";

const readLibrary = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
async function check(source, t) {
  const program = new CubicalProgram(await createCubical(), readLibrary, { collectReferences: false });
  t.after(() => program.dispose());
  const result = await program.check(source, "computability_sample");
  return { result, outcome: Object.fromEntries(result.outputs.map(output => [output.name, output.verified || output.reason])),
    gaps: program.gaps.filter(gap => gap.directive).map(gap => `${gap.name}: ${gap.reason}`) };
}

test("a computable declaration is rejected when it depends on an assumption, naming the path", async t => {
  const { outcome } = await check(`import classical;
computable def successor(n : Nat) := succ(n);
computable def uses_lem(P : U0, prop : Proposition(P), nn : (P -> Void) -> Void) : P {
  exact double_negation(P, prop, nn);
}
def after_failure := uses_lem;
def ordinary(P : U0, prop : Proposition(P), nn : (P -> Void) -> Void) : P {
  exact double_negation(P, prop, nn);
}
`, t);
  assert.equal(outcome.successor, true);
  assert.match(outcome.uses_lem, /depends on non-computing assumptions: LEM\(U0\), Truncate\(U0\), TruncateElim\(U0\)/);
  assert.match(outcome.uses_lem, /Path to LEM\(U0\): double_negation \(classical\) → LEM\(U0\)/);
  // A rejected declaration is not committed, so its dependents are blocked.
  assert.match(outcome.after_failure, /Untranslated dependency: uses_lem/);
  // Without the modifier the same proof is accepted, with its assumptions reported.
  assert.equal(outcome.ordinary, true);
});

test("evaluate checks the normal form of a closed assumption-free term", async t => {
  const { result, gaps } = await check(`import primes;
import classical;
import binary_arithmetic;
evaluate 2 + 2 expecting 4;
evaluate 2 + 2 expecting 5;
evaluate binary_mul(0b1101, 0b1011) expecting 0b10001111;
evaluate double_negation expecting double_negation;
evaluate 2 + 2 expecting tt;
`, t);
  assert.deepEqual(result.evaluations.map(evaluation => [evaluation.name, evaluation.value.slice(0, 1)]),
    [["at line 4", "4"], ["at line 6", "I"]]);
  assert.equal(gaps.length, 3);
  assert.match(gaps[0], /^evaluate at line 5: The term evaluates to 4, not 5\.$/);
  assert.match(gaps[1], /^evaluate at line 7: The evaluated term depends on non-computing assumptions: .*LEM\(U0\)/);
  assert.match(gaps[2], /^evaluate at line 8: The evaluated term has type .*, but the expected value has type /);
  assert.equal(result.complete, false, "a failed evaluation makes the module incomplete");
});

test("evaluation unfolds opaque definitions and ignores unfolding hints", async t => {
  const { result, gaps } = await check(`opaque def boxed(n : Nat) := succ(n);
def identity(n : Nat) := n;
evaluate boxed(1) expecting 2;
evaluate with unfolding [identity] { identity(boxed(2)) } expecting 3;
evaluate with unfolding [] { boxed(boxed(0)) } expecting boxed(1);
`, t);
  assert.deepEqual(gaps, []);
  assert.deepEqual(result.evaluations.map(evaluation => evaluation.value), ["2", "3", "2"]);
});

test("computable and evaluate parse, format stably and stay ordinary names elsewhere", () => {
  const source = `import primes;
computable def one := 1;
computable opaque def two := 2;
def uses_names(evaluate computable : Nat) : Nat {
  have expecting : Nat := evaluate;
  exact expecting;
}
evaluate one + one expecting two;
`;
  const ast = parse(source);
  assert.deepEqual(ast.declarations.map(d => [d.name.text, !!d.computable, !!d.opaque]),
    [["one", true, false], ["two", true, true], ["uses_names", false, false]]);
  assert.equal(ast.directives.filter(d => d.kind === "evaluate").length, 1);
  assert.equal("computable" in ast.declarations[2], false, "the flag appears only when written");
  const formatted = formatMathScript(source);
  assert.equal(formatMathScript(formatted), formatted);
  assert.match(formatted, /\ncomputable def one := 1;\n\ncomputable opaque def two := 2;\n\n/);
  assert.match(formatted, /\n\nevaluate one \+ one expecting two;\n$/);
  assert.match(formatted, /have expecting : Nat := evaluate;/);
});
