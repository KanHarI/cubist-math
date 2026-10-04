import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { checkTestModule } from "./check-program.mjs";

const module = await createCubical();
// The programs are cubist-tests/quotient_groups_*.cubist, whose
// comments state each refusal (tests/cubist-tests.test.mjs); here, the
// assumptions of the archive's lemmas and of the cases.
const cases = (t, name) => checkTestModule(t, name, { module, options: { collectReferences: false } });

test("quotient groups and the first isomorphism theorem check constructively across universes", async t => {
  const { program, result } = await cases(t, "quotient_groups_quotient_regression");
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.deepEqual(result.gaps, []);
  for (const binding of ["quotient_sets__quotient_is_set", "quotient_groups__QuotientGroup", "group_first_isomorphism__group_first_isomorphism"]) {
    const symbol = program.symbols[binding];
    assert.equal(symbol.verified, true, binding);
    const assumptions = symbol.axioms.map(name => program.checker.assumptionLabels.get(name) ?? name).sort();
    t.diagnostic(`${symbol.name}: ${JSON.stringify(assumptions)}`);
    assert.ok(assumptions.length > 0, "quotient construction must disclose truncation");
    assert.ok(assumptions.every(name => /Truncate|truncate|truncation/i.test(name)), JSON.stringify(assumptions));
  }
});

test("quotient construction rejects omitted normality and silent universe lowering", async t => {
  const { result } = await cases(t, "quotient_groups_invalid_quotient");
  assert.equal(result.complete, false);
  assert.equal(result.outputs.length, 2);
  assert.ok(result.outputs.every(d => !d.verified && !d.template));
  assert.ok(result.gaps.every(g => g.module === "quotient_groups_invalid_quotient"), JSON.stringify(result.gaps));
});
