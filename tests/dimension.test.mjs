import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { checkTestModule } from "./check-program.mjs";

const module = await createCubical();
// The programs are cubist-tests/dimension_*.cubist, whose comments state
// each refusal (tests/cubist-tests.test.mjs); here, the assumptions of the
// archive's lemmas they use.
const cases = (t, name) => checkTestModule(t, name, { module, options: { collectReferences: false } });
const checked = (program, name) => {
  const symbol = program.symbols[name];
  assert.equal(symbol?.verified, true, name);
  return symbol;
};
const axioms = (program, name) => checked(program, name).axioms.map(binding => program.checker.assumptionLabels.get(binding)).sort();

test("finite dimensions include zero, are unique for arbitrary bases, and need no choice", async t => {
  const { program, result } = await cases(t, "dimension_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.deepEqual(result.gaps, []);
  for (const name of ["coordinate_elimination__pivot_reduced_injective", "linear_constructions__linear_kernel_injective"])
    assert.deepEqual(axioms(program, name), [], name);
  const assumptions = axioms(program, "finite_dimension__finite_dimension_invariance");
  assert.ok(assumptions.includes("LEM"), JSON.stringify(assumptions));
  assert.ok(assumptions.every(name => /^(LEM|Truncate(?:Intro|Prop|Elim)?)$/.test(name)), JSON.stringify(assumptions));
  for (const name of ["dimension__finite_dimensional_prop", "dimension__dimension_unique", "dimension__dimension_linear_iso", "dimension__dimension_path"])
    assert.ok(axioms(program, name).every(name => /^(LEM|Truncate(?:Intro|Prop|Elim)?)$/.test(name)), name);
});

test("extension degree is positive, has identity degree one, and respects univalent extension equality", async t => {
  const { program, result } = await cases(t, "dimension_degree_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.deepEqual(result.gaps, []);
  for (const name of ["extension_degree__extension_degree_unique", "extension_degree__extension_degree_iso", "extension_degree__extension_dimension_not_zero"])
    assert.ok(axioms(program, name).every(name => /^(LEM|Truncate(?:Intro|Prop|Elim)?)$/.test(name)), name);
});

test("the product basis and numerical tower law check for arbitrary fields and a commuting triangle", async t => {
  const { program, result } = await cases(t, "dimension_tower_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.deepEqual(result.gaps, []);
  for (const name of ["scalar_restriction__field_tower_basis", "extension_degree__field_tower_basis_triangle"])
    assert.deepEqual(axioms(program, name), [], name);
  assert.ok(axioms(program, "extension_degree__extension_degree_tower").every(name => /^Truncate(?:Intro|Prop|Elim)?$/.test(name)));
  assert.ok(axioms(program, "extension_degree__tower_law").every(name => /^(LEM|Truncate(?:Intro|Prop|Elim)?)$/.test(name)));
  checked(program, "extension_degree__finite_extension_tower");
});

test("dimension does not choose a basis, forget linearity, or ignore a tower's embedding", async t => {
  const { program, result } = await cases(t, "dimension_invalid");
  assert.equal(result.outputs.length, 4);
  // Each refusal is the module's own: the archive it imports checks.
  assert.ok(result.gaps.every(gap => gap.module === "dimension_invalid"), JSON.stringify(result.gaps));
});
