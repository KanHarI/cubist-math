import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { parse } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { testModule } from "./check-program.mjs";

// computable and evaluate. The cases are cubist-tests/computability*.cubist,
// whose comments state each refusal and each failed evaluation
// (tests/cubist-tests.test.mjs); here, the values the evaluations compute,
// and the syntax.
const evaluation = testModule("computability_evaluation"), unfolding = testModule("computability_unfolding");

test("evaluate checks the normal form of a closed assumption-free term", async () => {
  const { result } = await evaluation();
  // Only the evaluations that pass have values; each that fails states its
  // error in the module.
  assert.deepEqual(result.evaluations.map(item => item.value), ["4", "0b10001111"]);
  assert.equal(result.complete, false, "a failed evaluation makes the module incomplete");
});
test("evaluation unfolds every definition and ignores unfolding hints", async () => {
  const { result } = await unfolding();
  assert.deepEqual(result.evaluations.map(item => item.value), ["2", "3", "2"]);
});
test("computable and evaluate parse, format stably and stay ordinary names elsewhere", () => {
  const source = `import primes;
computable def one := 1;
computable def two := 2;
def uses_names(evaluate, computable : Nat) : Nat {
  let expecting : Nat := evaluate;
  exact expecting;
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
  assert.match(formatted, /let expecting : Nat := evaluate;/);
});
