import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { parse } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { checkProgram, testModule } from "./check-program.mjs";

// computable and evaluate. The cases are cubist-tests/computability*.cubist,
// whose comments state each refusal, each failed evaluation and what each
// print shows (tests/cubist-tests.test.mjs); here, what a failed evaluation
// does to its module, the values evaluations report, and the syntax.
const evaluation = testModule("computability_evaluation");

test("evaluate reports the normal form, and a failed evaluation makes its module incomplete", async () => {
  const { result } = await evaluation();
  // Only the evaluations that pass have values; each that fails states its
  // error in the module.
  // The module selects unat, so the binary value is qualified (L2.10j).
  assert.deepEqual(result.evaluations.map(item => item.value), ["4", "bnat.(143)"]);
  assert.equal(result.complete, false, "a failed evaluation makes the module incomplete");
});
test("computable and evaluate parse and format stably; their keywords cannot be bound", () => {
  const source = `import unat;
computable def one := 1;
computable def two := 2;
def uses_names(computable_ : UNat) : UNat {
  let value : UNat := computable_;
  exact value;
}
evaluate one + one expecting two;
evaluate nonempty (Unit -> Unit) by fun x => x;
evaluate empty Void by fun x => x;
`;
  const ast = parse(source);
  assert.deepEqual(ast.declarations.map(d => [d.name.text, !!d.computable]),
    [["one", true], ["two", true], ["uses_names", false]]);
  assert.equal(ast.directives.filter(d => d.kind === "evaluate").length, 3);
  assert.equal("computable" in ast.declarations[2], false, "the flag appears only when written");
  const formatted = formatCubist(source);
  assert.equal(formatCubist(formatted), formatted);
  assert.match(formatted, /\ncomputable def one := 1;\n\ncomputable def two := 2;\n\n/);
  assert.match(formatted, /\n\nevaluate one \+ one expecting two;\n/);
  assert.match(formatted, /evaluate nonempty \(Unit -> Unit\) by fun x => x;\n/);
  assert.match(formatted, /let value : UNat := computable_;/);
  for (const word of ["computable", "evaluate", "expecting", "nonempty", "empty"])
    assert.throws(() => parse(`def f(${word} : UNat) : UNat := ${word};`),
      new RegExp(`^Error: ${word} is reserved, as a keyword or a built-in type of the language; pick another name\\.$`));
});


test("evidence assertions do not request normalization, while expected values do", async t => {
  const { program } = await checkProgram(t, "");
  const kernel = program.kernel, normalize = kernel.normalize.bind(kernel), normalizeFolded = kernel.normalizeFolded.bind(kernel);
  // Either normal form, full or folded (docs/roadmaps/historical/folded-normal-forms.md).
  let calls = 0;
  kernel.normalize = (...args) => { calls++; return normalize(...args); };
  kernel.normalizeFolded = (...args) => { calls++; return normalizeFolded(...args); };
  const evidence = await program.check(`
    evaluate nonempty (Void -> Void) by fun (x : Void) => absurd(x);
    evaluate empty Void by fun (x : Void) => x;
  `, "evidence", () => {}, { reuseModules: true });
  assert.equal(program.kernel, kernel, "the observation covers the kernel used by the directives");
  assert.deepEqual(evidence.gaps, []);
  assert.equal(calls, 0, "checking evidence must not expand its normal form");
  const ordinary = await program.check("evaluate tt expecting tt;", "ordinary", () => {}, { reuseModules: true });
  assert.deepEqual(ordinary.gaps, []);
  assert.ok(calls > 0, "ordinary expected-value evaluation still normalizes");
});
