import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { checkTestModule } from "./check-program.mjs";
const module = await createCubical();
// The programs are cubist-tests/linear_algebra_*.cubist, whose
// comments state each refusal (tests/cubist-tests.test.mjs); here, the
// assumptions of the archive's lemmas and of the cases.
const cases = (t, name) => checkTestModule(t, name, { module, options: { collectReferences: false } });

test("S3 has six elements and a genuinely non-normal point stabilizer, without axioms", async t => {
  const { program, result } = await cases(t, "linear_algebra_s3_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  for (const name of ["s3_has_six_elements", "s3_point_stabilizer_not_normal", "conjugate_swap12_moves_point0"]) {
    const symbol = program.symbols[`non_normal_subgroup__${name}`];
    assert.equal(symbol.verified, true, name);
    assert.deepEqual(symbol.axioms, [], name);
  }
});

test("finite bases give unique coordinates and cubical carrier transport without choice", async t => {
  const { program, result } = await cases(t, "linear_algebra_basis_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.deepEqual(result.gaps, []);
  for (const name of ["basis_coordinates_unique", "basis_carrier_path", "scalar_space_basis"]) {
    const symbol = program.symbols[`finite_bases__${name}`];
    assert.equal(symbol.verified, true, name); assert.deepEqual(symbol.axioms, [], name);
  }
});

test("nonlinear constant maps and a silently changed basis length are rejected", async t => {
  const { result } = await cases(t, "linear_algebra_invalid_linear");
  assert.equal(result.complete, false);
  assert.equal(result.outputs.length, 2);
  assert.ok(result.outputs.every(symbol => !symbol.verified));
  assert.ok(result.gaps.every(gap => gap.module === "linear_algebra_invalid_linear"), JSON.stringify(result.gaps));
});

test("spans are least subspaces and independent chains have bounds, including empty and U1-indexed chains", async t => {
  const { program, result } = await cases(t, "linear_algebra_chain_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.deepEqual(result.gaps, []);
  const checked = [
    ["finite_combinations", "linear_combination_append"], ["finite_combinations", "linear_combination_scale"],
    ["vector_subspaces", "span_least"], ["span_subspace", "SpanSubspace"], ["span_subspace", "span_idempotent_path"],
    ["independent_unions", "chain_union_independent"], ["independent_order", "independent_partial_order"],
    ["independent_order", "independent_union_least"],
  ];
  for (const [file, name] of checked) {
    const symbol = program.symbols[file + "__" + name];
    assert.equal(symbol.verified, true, name);
    const assumptions = symbol.axioms.map(binding => program.checker.assumptionLabels.get(binding));
    assert.ok(assumptions.every(name => /^Truncate/.test(name)), JSON.stringify(assumptions));
  }
  assert.deepEqual(program.symbols.independent_order__independent_partial_order.axioms, []);
});

test("the general basis theorem derives maximality from choice, with its exact assumptions visible", async t => {
  const { program, result } = await cases(t, "linear_algebra_general_basis_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  const assumptions = name => {
    const symbol = program.symbols[name];
    assert.equal(symbol?.verified, true, name);
    return symbol.axioms.map(binding => program.checker.assumptionLabels.get(binding)).sort();
  };
  for (const name of ["vector_arithmetic__vector_scale_injective", "finite_omission__fin_omit_cover",
    "finite_omission__linear_combination_omit", "chain_complete_orders__partial_order_is_set"])
    assert.deepEqual(assumptions(name), [], name);
  assert.ok(assumptions("bourbaki_witt__bourbaki_witt").every(name => /^(Truncate|LEM)/.test(name)));
  assert.ok(assumptions("independent_extension__adjoin_independent").every(name => /^(Truncate|LEM)/.test(name)));
  const basisAxioms = assumptions("vector_basis_existence__vector_space_has_basis");
  assert.ok(basisAxioms.includes("Choice"), JSON.stringify(basisAxioms));
  assert.ok(basisAxioms.includes("LEM"), JSON.stringify(basisAxioms));
  assert.ok(basisAxioms.every(name => /^(Choice|LEM|Truncate(?:Intro|Prop|Elim)?)$/.test(name)), JSON.stringify(basisAxioms));
  assert.deepEqual(assumptions("linear_algebra_general_basis_regression__any_vector_space"), basisAxioms);
});

test("basis existence cannot silently select a basis or justify adjoining the zero vector", async t => {
  const { result } = await cases(t, "linear_algebra_invalid_basis_selection");
  assert.equal(result.complete, false);
  assert.equal(result.outputs.length, 2);
  assert.ok(result.outputs.every(symbol => !symbol.verified));
  assert.ok(result.gaps.every(gap => gap.module === "linear_algebra_invalid_basis_selection"), JSON.stringify(result.gaps));
});
