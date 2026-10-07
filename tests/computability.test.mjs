import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { parse } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { testModule } from "./check-program.mjs";

// computable and evaluate. The cases are cubist-tests/computability*.cubist,
// whose comments state each refusal, each failed evaluation and what each
// print shows (tests/cubist-tests.test.mjs); here, what a failed evaluation
// does to its module, the values evaluations report, and the syntax.
const evaluation = testModule("computability_evaluation");

test("evaluate reports the normal form, and a failed evaluation makes its module incomplete", async () => {
  const { result } = await evaluation();
  // Only the evaluations that pass have values; each that fails states its
  // error in the module.
  // The module selects nat, so the binary value is qualified (L2.10j).
  assert.deepEqual(result.evaluations.map(item => item.value), ["4", "binary.(0b10001111)"]);
  assert.equal(result.complete, false, "a failed evaluation makes the module incomplete");
});
test("computable and evaluate parse, format stably and stay ordinary names elsewhere; expecting is reserved", () => {
  const source = `import primes;
computable def one := 1;
computable def two := 2;
def uses_names(evaluate, computable : Nat) : Nat {
  let value : Nat := evaluate;
  exact value;
}
evaluate one + one expecting two;
`;
  const ast = parse(source);
  assert.deepEqual(ast.declarations.map(d => [d.name.text, !!d.computable]),
    [["one", true], ["two", true], ["uses_names", false]]);
  assert.equal(ast.directives.filter(d => d.kind === "evaluate").length, 1);
  assert.equal("computable" in ast.declarations[2], false, "the flag appears only when written");
  const formatted = formatCubist(source);
  assert.equal(formatCubist(formatted), formatted);
  assert.match(formatted, /\ncomputable def one := 1;\n\ncomputable def two := 2;\n\n/);
  assert.match(formatted, /\n\nevaluate one \+ one expecting two;\n$/);
  assert.match(formatted, /let value : Nat := evaluate;/);
  assert.throws(() => parse("def f(expecting : Nat) : Nat := expecting;"),
    /^Error: expecting is reserved, as a keyword or a built-in type of the language; pick another name\.$/);
});
