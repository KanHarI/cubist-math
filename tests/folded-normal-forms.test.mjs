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
  const text = checker.displayText(checker.syntax.decode(result, checker.dimensions), checker.dimensions, { width: 1000, limit: 1000, reduce: 0 });
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

// Anywhere inside a !! part, under another mark too, and before anything is
// computed: far's first component, 512, is too deep for a full normal form
// (K344), which E486 comes before. Each is located at its own mark, even
// inside parentheses.
test("a !!! inside a !! part is refused, and !!! alone asks for the full normal form", async t => {
  const source = `import unat;
use unat;

def double(n : UNat) := n + n;
def pair_ : UNat and (UNat -> UNat) := (double(3), double);
def far : UNat and (Unit and Unit) := (2 * 256, (tt, tt));
inductive Box {
  box(u : Unit);
}
def boxed : Box := box(tt);
def sided : Unit or Unit := left(tt);
evaluate pair_ expecting !!(6, !!!_);
evaluate pair_ expecting (6, !!!_);
evaluate typed(Unit and Unit, (tt, tt)) expecting !!!(!!(!!!_), _);
evaluate far expecting (!!!_, !!(tt, !!!_));
evaluate pair_ expecting !!(6, (
  !!!_
));
evaluate sided expecting !!left(!!!_);
evaluate boxed expecting !!box(!!!_);
evaluate tt expecting !!typed(Unit, !!!_);
print(evaluate(!!!pair_));
`;
  const { result } = await checkProgram(t, source, { module });
  assert.deepEqual(result.gaps.map(gap => [gap.code, source.slice(gap.start, gap.end)]), Array(7).fill(["E486", "!!!"]));
  assert.deepEqual(result.gaps.map(gap => source.slice(0, gap.start).split("\n").length), [12, 14, 15, 17, 19, 20, 21]);
  assert.deepEqual(result.prints.map(print => print.text), ["(6, fun (n : UNat) => induction n return UNat { zero => n; succ h => succ(h); })"]);
});

// A !!! inside a !! part is refused before the evaluated term is elaborated:
// a numeral's reader (nat's literal rule) computes, and computes nothing
// here; nor does a part under a constructor, an injection or typed.
test("a !!! inside a !! part is refused before the evaluated literal computes", async t => {
  const { program } = await checkProgram(t, "", { module });
  const kernel = program.kernel;
  let calls = 0;
  for (const query of ["normalize", "normalizeFolded"]) {
    const original = kernel[query].bind(kernel);
    kernel[query] = handle => { calls++; return original(handle); };
  }
  const header = "import nat;\nuse nat;\n\ndef anchor : Unit := tt;\ndef sided : Nat or Unit := right(tt);\n";
  const warm = await program.check(header, "literal_warm", () => {}, { reuseModules: true });
  assert.deepEqual(warm.gaps, []);
  calls = 0;
  const result = await program.check(`${header}evaluate 5 expecting !!(!!!_);
evaluate sided expecting !!left(!!!_);
evaluate typed(Nat and Unit, (5, tt)) expecting !!typed(Nat and Unit, (!!!_, _));
`, "literal_refused", () => {}, { reuseModules: true });
  assert.deepEqual(result.gaps.map(gap => gap.code), ["E486", "E486", "E486"]);
  assert.equal(calls, 0, "no normal form is computed before E486");
});

// An exact value and a pattern's leaf are compared with the value's folded
// normal form by conversion: a and b are distinct definitions of one
// function, so pa and pb fold apart, to (a, 1) and (b, 1).
test("an expected value is compared with a folded normal form by conversion", async t => {
  const source = `import unat;
use unat;

def a(n : UNat) : UNat := n;
def b(n : UNat) : UNat := n;
def c(n : UNat) : UNat := n + 1;
def pa : (UNat -> UNat) and UNat := (a, 1);
def pb : (UNat -> UNat) and UNat := (b, 1);
def pc : (UNat -> UNat) and UNat := (c, 1);
def nested : ((UNat -> UNat) and UNat) and UNat := (pa, 1);
evaluate pa expecting pb;
evaluate nested expecting (pb, _);
evaluate pa expecting pc;
evaluate nested expecting (pc, _);
`;
  const { result } = await checkProgram(t, source, { module });
  assert.deepEqual(result.evaluations.map(evaluation => evaluation.value), ["(a, 1)", "((a, 1), <unevaluated>)"]);
  assert.deepEqual(result.gaps.map(gap => [gap.code, source.slice(0, gap.start).split("\n").length]), [["E326", 13], ["E477", 14]]);
});

// Each caller asks for the normal form its table row in the note assigns:
// an exact value, folded; a witness, full; !! folded and !!! full.
test("exact values fold, and !!! and witness ask for the full normal form", async t => {
  const { program } = await checkProgram(t, "", { module });
  const kernel = program.kernel, asked = [];
  for (const query of ["normalize", "normalizeFolded"]) {
    const original = kernel[query].bind(kernel);
    kernel[query] = handle => { asked.push(query); return original(handle); };
  }
  // Each source a module of its own name, which reuseModules keeps apart.
  let runs = 0;
  const run = async source => {
    asked.length = 0;
    const result = await program.check(`import h1_truncation;\nuse unat;\n${source}`, `routing_${runs++}`, () => {}, { reuseModules: true });
    assert.deepEqual(result.gaps, [], source);
    return [...new Set(asked)];
  };
  assert.deepEqual(await run("evaluate 2 + 2 expecting 4;"), ["normalizeFolded"]);
  assert.deepEqual(await run("evaluate 2 + 2 expecting !!_;"), ["normalizeFolded"]);
  assert.deepEqual(await run("evaluate 2 + 2 expecting !!!_;"), ["normalize"]);
  assert.deepEqual(await run("print(witness(typed(Trunc(U0, UNat), point(3))));"), ["normalize"]);
});

// The term asked for is unfolded even where one step takes it to a stuck
// elimination: f is eta its eliminator, so f(x) steps straight to it, and
// the folded normal form shows that eliminator, as the weak head does; and
// so where f(x) is applied, projected or applied to a dimension, whose
// step takes f(x)'s weak head in steps of its own.
test("the term asked for is unfolded where a definition is eta an eliminator", async t => {
  const { program, verdicts } = await checkProgram(t, `inductive N {
  zero;
  succ(k : N);
}

def f(n : N) := match n return N { zero => zero; succ(k) => k; };

def computes_f := match zero return N -> N { zero => f; succ(k) => f; };

def shift(n : N) := match n return N -> N { zero => fun (m : N) => m; succ(k) => fun (m : N) => k; };

def halves(n : N) := match n return N and N { zero => (zero, zero); succ(k) => (k, k); };

def constant(n : N) := match n return zero = zero { zero => refl(zero); succ(k) => refl(zero); };
`, { module });
  for (const name of ["f", "computes_f", "shift", "halves", "constant"]) assert.equal(verdicts[name], true, name);
  const { kernel, checker } = program;
  const value = name => kernel.definition(kernel.definitions.get(`main__${name}`));
  const domain = checker.syntax.decode(value("f").type).domain, x = { tag: "Var", name: "x" };
  // The root of an application, level application, projection or path
  // application spine.
  const root = handle => {
    let term = checker.syntax.decode(handle, new Map([["i", 0]]));
    while (["App", "LApp", "Fst", "Snd", "PApp"].includes(term.tag)) term = term.fn ?? term.pair ?? term.path;
    return term.tag;
  };
  const at = name => ({ tag: "App", fn: { tag: "DefRef", name: `main__${name}` }, arg: x });
  // f(x) itself, and a match by cases on zero that computes f, applied to x:
  // another eliminator at the root, even of the same kind, is no rebuild.
  const computed = { tag: "App", fn: checker.syntax.decode(value("computes_f").value), arg: x };
  const terms = [at("f"), computed, { tag: "App", fn: at("shift"), arg: x },
    { tag: "Fst", pair: at("halves") }, { tag: "Snd", pair: at("halves") }, { tag: "PApp", path: at("constant"), arg: [["i:1"]] }];
  for (const term of terms) {
    const { expression } = checker.checkSyntax(term, null, new Map([["x", domain]]), new Map([["i", 0]]));
    assert.equal(root(kernel.head(expression)), "Elim", term.tag);
    assert.equal(root(kernel.normalizeFolded(expression)), "Elim", term.tag);
    assert.equal(root(kernel.normalize(expression)), "Elim", term.tag);
  }
  // shift's eliminator stuck on f(x), applied to x: the step rebuilt it in
  // place, its scrutinee reduced, so f(x) stays as written there.
  const shifted = checker.syntax.decode(value("shift").value);
  const eliminator = shifted.tag === "Lam" && shifted.body.tag === "App" ? shifted.body.fn : shifted;
  assert.equal(eliminator.tag, "Elim");
  const stuck = { tag: "App", fn: { tag: "App", fn: eliminator, arg: at("f") }, arg: x };
  const { expression } = checker.checkSyntax(stuck, null, new Map([["x", domain]]), new Map());
  const scrutinee = handle => checker.syntax.decode(handle).fn.arg;
  assert.equal(scrutinee(kernel.normalizeFolded(expression)).fn.tag, "DefRef");
  assert.equal(scrutinee(kernel.normalize(expression)).fn.tag, "Elim");
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
    shown.push(checker.displayText(checker.syntax.decode(kernel.normalizeFolded(expression)), [], { width: 1000, limit: 1000, notation: {}, reduce: 0 }));
  }
  assert.equal(shown[0], shown[1]);
});
