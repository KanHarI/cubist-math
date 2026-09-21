import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
const module = await createCubical();
const readSource = name => readFile(new URL(`../web/proofs/${name}.cubist`, import.meta.url), "utf8");
const create = t => {
  const program = new CubicalProgram(module, readSource, { collectReferences: false });
  t.after(() => program.dispose()); return program;
};

test("S3 has six elements and a genuinely non-normal point stabilizer, without axioms", async t => {
  const program = create(t);
  const result = await program.check("import non_normal_subgroup; theorem verified_example : IsNormal(S3, S3PointStabilizer) -> Void { exact s3_point_stabilizer_not_normal; }", "s3_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  for (const name of ["s3_has_six_elements", "s3_point_stabilizer_not_normal", "conjugate_swap12_moves_point0"]) {
    const symbol = program.symbols[`non_normal_subgroup__${name}`];
    assert.equal(symbol.verified, true, name);
    assert.deepEqual(symbol.axioms, [], name);
  }
});

test("finite bases give unique coordinates and cubical carrier transport without choice", async t => {
  const program = create(t);
  const result = await program.check(`import linear_span;
    import finite_fields;
    theorem f2_basis : FiniteBasis(F2, ScalarSpace(F2), 1) { exact scalar_space_basis(F2); }
    theorem f4_basis_over_itself : FiniteBasis(F4, ScalarSpace(F4), 1) { exact scalar_space_basis(F4); }
    theorem coordinate_plane_basis(K : AlgebraicField) : FiniteBasis(K, CoordinateSpace(K, 2), 2) {
      exact standard_basis(K, 2);
    }
    theorem scalar_transport_computes(K : AlgebraicField, x : af_carrier(K)) :
      transport((fun (A : U0) => A), (Fin(1) -> af_carrier(K)), af_carrier(K),
        ua(U0, (Fin(1) -> af_carrier(K)), af_carrier(K),
          linear_iso_equiv(K, CoordinateSpace(K, 1), ScalarSpace(K), scalar_space_basis(K))),
        (fun (i : Fin(1)) => x)) = x {
      exact UnivalenceBeta(U0, (Fin(1) -> af_carrier(K)), af_carrier(K),
        linear_iso_equiv(K, CoordinateSpace(K, 1), ScalarSpace(K), scalar_space_basis(K)),
        (fun (i : Fin(1)) => x));
    }
  `, "basis_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.deepEqual(result.gaps, []);
  for (const symbol of result.outputs) {
    assert.equal(symbol.verified, true, symbol.name);
    assert.deepEqual(symbol.axioms, [], symbol.name);
  }
  for (const name of ["basis_coordinates_unique", "basis_carrier_path", "scalar_space_basis"]) {
    const symbol = program.symbols[`finite_bases__${name}`];
    assert.equal(symbol.verified, true, name); assert.deepEqual(symbol.axioms, [], name);
  }
});

test("nonlinear constant maps and a silently changed basis length are rejected", async t => {
  const program = create(t);
  const result = await program.check(`import finite_bases;
    import finite_fields;
    def constant_one_is_not_linear : LinearMap(F2, ScalarSpace(F2), ScalarSpace(F2)) {
      exact ((fun (x : F2Carrier) => f2_1),
        (fun (x : F2Carrier) => fun (y : F2Carrier) => refl(f2_1)),
        (fun (a : F2Carrier) => fun (x : F2Carrier) => refl(f2_1)));
    }
    def wrong_basis(K : AlgebraicField) : FiniteBasis(K, CoordinateSpace(K, 0), 1) {
      exact standard_basis(K, 1);
    }
  `, "invalid_linear");
  assert.equal(result.complete, false);
  assert.equal(result.outputs.length, 2);
  assert.ok(result.outputs.every(symbol => !symbol.verified));
  assert.ok(result.gaps.every(gap => gap.module === "invalid_linear"), JSON.stringify(result.gaps));
});
