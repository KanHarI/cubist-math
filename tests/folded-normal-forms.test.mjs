import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { checkProgram } from "./check-program.mjs";

// The folded normal form (docs/roadmaps/runtime/folded-normal-forms.md),
// through the kernel's JavaScript interface: closed data computes in full,
// and a definition whose weak head is no data stays as written.
const module = await createCubical();
const source = `import rationals;
use unat;

def two_thirds := rationals.(2/3);

def product := unat.(5) * unat.(3);

def numbers := typed(UNat and UNat, (unat.(2) + unat.(2), unat.(7)));

def glued : Glue(UNat) := glue(unat.(1) + unat.(1));

def glued_pair := typed(Glue(UNat) and Unit, (glued, tt));
`;

const folded = (program, name) => {
  const { kernel, checker } = program;
  const expression = checker.checkSyntax({ tag: "DefRef", name: `main__${name}` }, null, new Map(), new Map()).expression;
  return { kernel, checker, expression, folded: kernel.normalizeFolded(expression) };
};

test("a rational literal's folded normal form names its certificate", async t => {
  const { program, verdicts } = await checkProgram(t, source, { module });
  assert.equal(verdicts.two_thirds, true);
  const before = program.kernel.work().querySteps;
  const { checker, folded: result } = folded(program, "two_thirds");
  // Its full normal form is 70M ticks and over a million nodes.
  assert.ok(program.kernel.work().querySteps - before < 1000000);
  const text = checker.displayText(checker.syntax.decode(result, checker.dimensions), 1000, 1000, checker.notation ?? {}, 0);
  assert.equal(text, "class((class((unat.(2), unat.(0))), class((unat.(3), unat.(0))), int_succ_nonzero(unat.(2))))");
});

test("closed data has the same folded and full normal forms", async t => {
  const { program, verdicts } = await checkProgram(t, source, { module });
  // A glued element is data too: glued computes to glue(2) inside the pair.
  for (const name of ["product", "numbers", "glued_pair"]) {
    assert.equal(verdicts[name], true, name);
    const { kernel, expression, folded: result } = folded(program, name);
    assert.ok(kernel.alphaEqual(result, kernel.normalize(expression)), name);
  }
});

test("the folded normal form is asked of derived terms only", async t => {
  const { program } = await checkProgram(t, source, { module });
  const raw = program.kernel.term("Unit", 0);
  assert.throws(() => program.kernel.normalizeFolded(raw), /Normalize a term or type an instruction derived/);
});

// The marks (FN2): !! computes the folded normal form, !!! the full one; an
// exact expected value is compared by the folded normal forms of both sides.
test("!! prints a literal folded, and an exact rational value is compared folded", async t => {
  const { program, result } = await checkProgram(t, `import rationals;
use unat;

print(evaluate(!!rationals.(2/3)));
evaluate rationals.(2/3) expecting rationals.(2/3);
`, { module });
  assert.deepEqual(result.gaps, []);
  assert.deepEqual(result.prints.map(print => print.text), ["class((class((2, 0)), class((3, 0)), int_succ_nonzero(2)))"]);
  // Both sides' full normal forms are 70M ticks each.
  assert.ok(program.kernel.work().querySteps < 10000000n, String(program.kernel.work().querySteps));
});

test("a !!! inside a !! part is refused, and !!! alone asks for the full normal form", async t => {
  const { result } = await checkProgram(t, `import unat;
use unat;

def double(n : UNat) := n + n;
def pair_ : UNat and (UNat -> UNat) := (double(3), double);
evaluate pair_ expecting !!(6, !!!_);
evaluate pair_ expecting (6, !!!_);
print(evaluate(!!!pair_));
`, { module });
  assert.deepEqual(result.gaps.map(gap => gap.code), ["E486"]);
  assert.deepEqual(result.prints.map(print => print.text), ["(6, fun (n : UNat) => induction n return UNat { zero => n; succ h => succ(h); })"]);
});
