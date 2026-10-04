import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { checkTestModule } from "./check-program.mjs";

const module = await createCubical();
// The programs are cubist-tests/quotient_universal_*.cubist, whose
// comments state each refusal (tests/cubist-tests.test.mjs); here, the
// assumptions of the archive's lemmas and of the cases.
const cases = (t, name) => checkTestModule(t, name, { module, options: { collectReferences: false } });

// The homomorphism universe schemas are
// cubist-tests/quotient_universal_hom_universe_regression.cubist.

test("quotient universal property works for genuinely U1 targets without representative choice", async t => {
  const { program, result } = await cases(t, "quotient_universal_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.deepEqual(result.gaps, []);
  for (const binding of ["quotient_group_universal__quotient_group_universal", "quotient_group_universal__quotient_projection_epimorphism", "quotient_universal_regression__projection_descends_to_identity"]) {
    const symbol = program.symbols[binding];
    assert.equal(symbol.verified, true, binding);
    const assumptions = symbol.axioms.map(name => program.checker.assumptionLabels.get(name) ?? name).sort();
    t.diagnostic(`${symbol.name}: ${JSON.stringify(assumptions)}`);
    assert.ok(assumptions.length > 0);
    assert.ok(assumptions.every(name => /^Truncate(?:Intro|Elim|Prop)?$/.test(name)), JSON.stringify(assumptions));
  }
});

test("factorization cannot omit the subgroup-killing hypothesis", async t => {
  const { result } = await cases(t, "quotient_universal_bad_factorization");
  assert.equal(result.complete, false);
  assert.equal(result.outputs.length, 1);
  assert.equal(result.outputs[0].verified, false);
  assert.ok(result.gaps.every(gap => gap.module === "quotient_universal_bad_factorization"), JSON.stringify(result.gaps));
});
