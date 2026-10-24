import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
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

// The term asked for is unfolded even where one step takes it to a stuck
// elimination: f is eta its eliminator, so f(x) steps straight to it, and
// the folded normal form shows that eliminator, as the weak head does.
test("the term asked for is unfolded where a definition is eta an eliminator", async t => {
  const { program, verdicts } = await checkProgram(t, `inductive N {
  zero;
  succ(k : N);
}

def f(n : N) := match n return N { zero => zero; succ(k) => k; };

def chooser := match zero return N -> N { zero => f; succ(k) => f; };
`, { module });
  assert.equal(verdicts.f, true);
  assert.equal(verdicts.chooser, true);
  const { kernel, checker } = program;
  const value = name => kernel.definition(kernel.definitions.get(`main__${name}`));
  const domain = checker.syntax.decode(value("f").type).domain, x = { tag: "Var", name: "x" };
  const root = handle => kernel.spine(handle).root.kind;
  // f(x) itself, and a match by cases on zero that computes f, applied to x:
  // another eliminator at the root, even of the same kind, is no rebuild.
  const applied = { tag: "App", fn: { tag: "DefRef", name: "main__f" }, arg: x };
  const chosen = { tag: "App", fn: checker.syntax.decode(value("chooser").value), arg: x };
  for (const term of [applied, chosen]) {
    const { expression } = checker.checkSyntax(term, null, new Map([["x", domain]]), new Map());
    assert.equal(root(kernel.head(expression)), "Elim");
    assert.equal(root(kernel.normalizeFolded(expression)), "Elim");
    assert.equal(root(kernel.normalize(expression)), "Elim");
  }
});

// The folded normal form does not depend on syntax interning. f's
// eliminator, read back and checked again, is f's own node with interning
// and a copy without; applied to box(f(x)) it computes f's eliminator at x,
// which is no rebuild of it in place, in either mode.
test("interning does not change a folded normal form", async t => {
  const shown = [];
  for (const shareSyntax of [true, false]) {
    const program = new CubicalProgram(module, sourceReader(), { collectReferences: false, optimizations: { shareSyntax } });
    t.after(() => program.dispose());
    const result = await program.check(`inductive Box {
  box(g : Unit -> Unit);
}

def f(s : Box) := match s return Unit -> Unit { box(g) => g; };
`, "main");
    assert.deepEqual(result.gaps, []);
    const { kernel, checker } = program, f = kernel.definition(kernel.definitions.get("main__f"));
    const domain = checker.syntax.decode(f.type).domain, value = checker.syntax.decode(f.value);
    const eliminator = value.tag === "Lam" && value.body.tag === "App" ? value.body.fn : value;
    assert.equal(eliminator.tag, "Elim");
    const x = { tag: "Var", name: "x" };
    const boxed = { tag: "App", fn: { tag: "Con", index: 0, sort: domain }, arg: { tag: "App", fn: { tag: "DefRef", name: "main__f" }, arg: x } };
    const term = { tag: "App", fn: { tag: "App", fn: eliminator, arg: boxed }, arg: { tag: "Point" } };
    const { expression } = checker.checkSyntax(term, null, new Map([["x", domain]]), new Map());
    shown.push(checker.displayText(checker.syntax.decode(kernel.normalizeFolded(expression)), 1000, 1000, {}, 0));
  }
  assert.equal(shown[0], shown[1]);
});
