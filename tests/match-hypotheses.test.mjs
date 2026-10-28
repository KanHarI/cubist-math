// A match expression takes each hypothesis about its matched variable at
// each constructor, as the match statement does (work-plan L2.2a). The cases
// are cubist-tests/match_hypotheses.cubist, whose comments state that the
// module checks without errors or warnings (tests/cubist-tests.test.mjs);
// here each case is checked by name, the computations are compared, and the
// expression's terms are compared with the statement's.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { canonicalHasher } from "../tools/canonical-hash.mjs";
import { testModule } from "./check-program.mjs";

const module = await createCubical();
const cases = testModule("match_hypotheses", { module });
const ok = declaration => assert.ok(declaration.verified, `${declaration.name}: ${declaration.reason}`);

// Each was refused before: its kernel check met a hypothesis at the
// matched variable rather than at the clause's constructor.
const narrowed = ["le_zero_absurd", "le_trans_expression", "subtract", "pass_whole", "pass_below", "inner_last",
  "inner_first", "le_zero_return", "last_only", "nil_of"];
// Each checked before, and checks still.
const unchanged = ["le_zero_typed", "positive_first", "le_zero_curried", "pass_below_eta", "le_step",
  "le_zero_statement", "le_trans_statement", "le_zero_kept", "count", "count_into", "circle_kept", "merely_kept"];

test("a match expression takes a hypothesis about its variable at each constructor", async () => {
  const { get } = await cases();
  for (const name of [...narrowed, ...unchanged]) {
    ok(get(name));
    assert.deepEqual(get(name).axioms, [], `${name} uses no assumption`);
  }
});

test("the narrowed definitions compute", async () => {
  const { result } = await cases();
  assert.deepEqual(result.evaluations.map(evaluation => evaluation.value), ["3", "1", "5"]);
  assert.deepEqual(result.gaps.filter(gap => gap.directive), []);
});

// One implementation: the expression's motive and clauses are the
// statement's, so the checked terms are the same up to bound names.
test("the expression and the statement elaborate to the same terms", async () => {
  const { program } = await cases();
  const views = program.checker.definitionViews, hash = canonicalHasher();
  const term = name => {
    const view = views.get(`match_hypotheses__${name}`);
    assert.ok(view, `no checked definition ${name}`);
    return hash(view.term);
  };
  assert.equal(term("le_zero_absurd"), term("le_zero_statement"));
  assert.equal(term("le_trans_expression"), term("le_trans_statement"));
  assert.notEqual(term("le_zero_absurd"), term("le_zero_typed"), "typed(Void, h) adds an ascription");
});
