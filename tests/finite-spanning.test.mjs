import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { checkTestModule } from "./check-program.mjs";
const module = await createCubical();
// The programs are cubist-tests/finite_spanning_*.cubist, whose
// comments state each refusal (tests/cubist-tests.test.mjs); here, the
// assumptions of the archive's lemmas and of the cases.
const cases = (t, name) => checkTestModule(t, name, { module, options: { collectReferences: false } });
const assumptions = (p, name) => { const s = p.symbols[name]; assert.equal(s?.verified, true, name); return s.axioms.map(id => p.checker.assumptionLabels.get(id)); };

test("finite spanning families contain an indexed subfamily basis without choice", async t => {
  const { program: p, result } = await cases(t, "finite_spanning_spanning_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  for (const name of ["finite_linear_lifts__finite_linear_lift", "spanning_subfamilies__finite_spanning_subfamily_basis", "finite_spanning__finite_spanning_basis"])
    assert.ok(assumptions(p, name).every(a => /^(LEM|Truncate(?:Intro|Prop|Elim)?)$/.test(a)), name);
});

test("arbitrary finite subspaces have bases and finiteness descends both ways in a tower", async t => {
  const { program: p, result } = await cases(t, "finite_spanning_finite_tower_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  for (const name of ["subspace_carriers__finite_subspace_basis", "finite_towers__finite_extension_tower_iff"])
    assert.ok(assumptions(p, name).every(a => /^(LEM|Truncate(?:Intro|Prop|Elim)?)$/.test(a)), name);
  assert.deepEqual(assumptions(p, "subspace_carriers__SubspaceVectorSpace"), []);
});

test("finite extraction does not choose a basis or equate finiteness with independence", async t => {
  const { result } = await cases(t, "finite_spanning_invalid_spanning");
  assert.equal(result.complete, false);
  assert.equal(result.outputs.length, 2);
  assert.ok(result.outputs.every(s => !s.verified));
  assert.ok(result.gaps.every(g => g.module === "finite_spanning_invalid_spanning"), JSON.stringify(result.gaps));
});
