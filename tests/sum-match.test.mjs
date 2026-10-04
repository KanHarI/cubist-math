// The match statement on a sum (work-plan L2.2a), which replaced cases: what
// the verdicts of cubist-tests/sum_match.cubist do not show. Each clause's
// goal is the goal at its side; a goal that does not depend on the value is
// the motive itself, the term cases made; and cases is refused with its
// match form, while a historical source reads in today's syntax.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { parse } from "../web/cubist/parser.mjs";
import { currentSyntax } from "../web/cubist/legacy-syntax.mjs";
import { freeNames } from "../web/translator/core.mjs";
import { testModule } from "./check-program.mjs";

const cases = testModule("sum_match", { module: await createCubical() });

// The first SumRec in a term.
function sumrec(term) {
  if (!term || typeof term !== "object") return null;
  if (term.tag === "SumRec") return term;
  for (const child of Object.values(term)) {
    const found = sumrec(child);
    if (found) return found;
  }
  return null;
}

test("each clause proves the goal at its side, hypotheses included", async () => {
  const { program } = await cases();
  const goals = name => program.steps("sum_match").filter(step => step.declaration === name).map(step => [step.kind, step.goal]);
  assert.deepEqual(goals("sides"), [
    ["matchStatement", "(exists a : A. s = left(a)) or (exists b : B. s = right(b))"],
    ["exact", "(exists a1 : A. left(a) = left(a1)) or (exists b : B. left(a) = right(b))"],
    ["exact", "(exists a : A. right(b) = left(a)) or (exists b1 : B. right(b) = right(b1))"]]);
  assert.deepEqual(goals("kept"), [["matchStatement", "s = s"], ["exact", "left(a) = left(a)"], ["exact", "right(b) = right(b)"]]);
});

test("a goal that does not depend on the value is the motive, as cases made it", async () => {
  const { program } = await cases();
  const eliminated = name => sumrec(program.checker.definitionViews.get(`sum_match__${name}`).term);
  const motive = name => eliminated(name).motive;
  // After intro, the goal is a redex over the value that drops it: kept as
  // it is, not abstracted.
  for (const name of ["swapped", "swapped_intro"]) {
    const { tag, name: binder, body } = motive(name);
    assert.equal(tag, "Lam");
    assert.ok(!freeNames(body).has(binder), `${name}'s motive does not use its binder`);
  }
  assert.ok(freeNames(motive("swapped_intro").body).has(eliminated("swapped_intro").value.name), "the redex is kept");
  const dependent = motive("sides");
  assert.ok(freeNames(dependent.body).has(dependent.name), "a goal about the value is abstracted");
});

test("cases is refused with its match form; a historical cases reads as match", () => {
  const parseError = source => { try { parse(source); return null; } catch (error) { return error.message; } };
  const historical = "def d(A : U0, p : A or A) : A { cases p { left x => { exact x; } right y => { exact y; } } }";
  assert.equal(parseError(historical), "cases was removed: write match value { left(a) => { … } right(b) => { … } }.");
  assert.equal(currentSyntax(historical),
    "def d(A : U0, p : A or A) : A { match p { left x => { exact x; } right y => { exact y; } } }");
  assert.equal(parseError(currentSyntax(historical)), null);
  // Prose is left alone.
  assert.equal(currentSyntax("// in both cases { left as is"), "// in both cases { left as is");
});
