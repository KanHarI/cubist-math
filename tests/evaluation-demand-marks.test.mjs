import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import createCubical from "../web/dist/cubical.mjs";
import { tokenize, parse } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { lint } from "../web/cubist/lint.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { checkProgram } from "./check-program.mjs";
import { normalDigest, sharedNormalDigest } from "../tools/evaluation-baseline.mjs";
import { reported } from "../tools/inline-errors.mjs";
import { printedNodes, valueForm } from "../web/translator/evaluation.mjs";
import { Translator } from "../web/translator/translate.mjs";

// Evaluation demand marks (docs/roadmaps/historical/evaluation-demand-marks.md):
// `!` asks for a part's weak head, `!!` for its normal form, stuck
// definitions folded, and `!!!` for its full normal form, and an
// unmarked part of a pattern is computed only as far as the pattern observes
// it. The cases with messages are cubist-tests/evaluate_patterns.cubist;
// here, the tokens, the values evaluations report, what is left uncomputed,
// the normalize guard, and every construct of the language.
const module = await createCubical();

// A program that records what evaluation asks the kernel: for each term
// checked for evaluation that names a definition, whether the whole term was
// normalized while it was the latest, the normal form the kernel gave, read
// back here, and the term then displayed, or, for a term shown without its
// normal form, the root of its weak head; and every handle a weak head or a
// normal form was asked of.
function recordedProgram(t) {
  const program = new CubicalProgram(module, sourceReader());
  t.after(() => program.dispose());
  const { checker, kernel } = program, evaluations = [], asked = [];
  const { evaluated, displayText } = checker, { head, normalize, normalizeFolded } = kernel;
  // The first term displayed after the latest evaluation's normalization is
  // its value; later ones are other directives'.
  checker.displayText = function (term, ...rest) {
    const latest = evaluations.at(-1);
    if (latest?.normalized && !("shown" in latest)) latest.shown = term;
    // A value shown without its normal form, and the root of the weak head
    // the kernel computes for the term, asked here apart from derivedHead
    // while the term's handles are live.
    if (latest && !latest.normalized && !("displayed" in latest)) {
      latest.displayed = term;
      try { latest.root = checker.decoded(kernel.spine(head.call(kernel, latest.handle)).root.id); }
      catch { latest.root = null; }
    }
    return displayText.call(this, term, ...rest);
  };
  checker.evaluated = function (term, ...rest) {
    const result = evaluated.call(this, term, ...rest);
    if (term.tag === "DefRef") evaluations.push({ name: term.name, handle: result.expression, normalized: false, heads: [] });
    return result;
  };
  kernel.head = function (handle) {
    const result = head.call(this, handle);
    asked.push({ query: "head", handle, result });
    return result;
  };
  // Directives run in turn, and a later one may check the same term to the
  // same handle: the normalization is the latest evaluation's, folded or full
  // (docs/roadmaps/historical/folded-normal-forms.md).
  const normalizing = (query, folded) => function (handle) {
    asked.push({ query, handle });
    const result = query === "normalize" ? normalize.call(this, handle) : normalizeFolded.call(this, handle);
    if (evaluations.at(-1)?.handle === handle) Object.assign(evaluations.at(-1), { normalized: true, folded, normal: checker.decoded(result) });
    return result;
  };
  kernel.normalize = normalizing("normalize", false);
  kernel.normalizeFolded = normalizing("normalizeFolded", true);
  return { program, evaluations, asked };
}

test("!, !! and !!! are tokens, read only right after evaluate and in an expected pattern", () => {
  assert.deepEqual(tokenize("!!!_ !!_ !_ ! !").slice(0, -1).map(token => token.text), ["!!!", "_", "!!", "_", "!", "_", "!", "!"]);
  assert.deepEqual(tokenize("!!!!").slice(0, -1).map(token => token.text), ["!!!", "!"]);
  const [directive] = parse("evaluate !!e expecting (!_, cons(1, !!!_));").directives;
  assert.equal(directive.mark, "!!");
  assert.equal(directive.expected.left.kind, "demand");
  assert.equal(directive.expected.left.mark, "!");
  assert.equal(directive.expected.right.args[1].mark, "!!!");
  // Marks apart would read as one but ask for less: each is refused.
  for (const source of ["evaluate e expecting ! !_;", "evaluate ! !e expecting _;", "evaluate e expecting !! !_;",
    "evaluate e expecting ! !!_;", "evaluate !!! !e expecting _;", "evaluate e expecting !!!!_;"])
    assert.throws(() => parse(source), /Two demand marks in a row, .+, ask for one demand/, source);
  // print(evaluate(…)) takes a mark before its term, and nowhere else.
  assert.equal(parse("print(evaluate(!!e));").directives[0].mark, "!!");
  assert.equal(parse("print(evaluate(!!!e));").directives[0].mark, "!!!");
  for (const source of ["def x := !3;", "evaluate !(!e) expecting _;", "print(typeof(!e));", "print(evaluate(f(!e)));"])
    assert.throws(() => parse(source), /The demand mark ! stands right after evaluate/, source);
  assert.throws(() => parse("print(typeof(!!!e));"), /The demand mark !!! stands right after evaluate/);
});

test("a pattern computes what it observes, and the value is shown as far as it was computed", async t => {
  const { result } = await checkProgram(t, `import unat;
import lists;
use unat;
def pairs : UNat and (Unit or UNat) := (3, right(2 + 2));
def numbers : List(U0, UNat) := cons(1, cons(2, nil));
def successor := fun (n : UNat) => succ(n);
def twice := fun (n : UNat) => n + n;
def far : UNat and UNat := (1, 2 * 256);
def copy := fun (n : UNat) => induction n return UNat { zero => 0; succ h => succ(h); };
evaluate pairs expecting (3, _);
evaluate pairs expecting !_;
evaluate pairs expecting !!_;
evaluate !pairs expecting (_, !_);
evaluate numbers expecting cons(1, !_);
evaluate numbers expecting cons(_, !!_);
evaluate successor expecting !_;
evaluate twice expecting !_;
evaluate UNat expecting !_;
evaluate far expecting (1, succ(_));
evaluate copy expecting !_;
`, { module });
  assert.deepEqual(result.gaps.map(gap => gap.reason), []);
  assert.deepEqual(result.evaluations.map(evaluation => evaluation.value), [
    "(3, <unevaluated>)",
    "(<unevaluated>, <unevaluated>)",
    "(3, right(4))",
    "(<unevaluated>, right(<unevaluated>))",
    "cons(1, cons(<unevaluated>, <unevaluated>))",
    "cons(<unevaluated>, cons(2, nil))",
    // Eta makes a successor function's weak head the constructor.
    "succ",
    "<fun>",
    "<type>",
    "(1, succ(<unevaluated>))",
    // Eta makes it the eliminator alone, a function too.
    "<fun>",
  ]);
});

test("a part's failed demand is located at that part of the pattern, with the kernel's code", async t => {
  const source = `import unat;
use unat;
def far : UNat and UNat := (2 * 255, 1);
evaluate far
  expecting (
    2 * 255,
    _);
evaluate far
  expecting (_, !!_
  );
def ones : UNat and UNat := (1, 1);
evaluate ones
  expecting !!(
    2 * 255, _);
evaluate far
  expecting !!(_, _
  );
`;
  const { result } = await checkProgram(t, source, { module });
  // The leaf under !! fails its comparison; the !! of far fails itself, as
  // the pair's normal form is a level deeper than its first component's.
  assert.deepEqual(result.gaps.map(gap => [gap.code, source.slice(gap.start, gap.end)]),
    [["K344", "2 * 255"], ["K344", "2 * 255"], ["K344", "!!(_, _\n  )"]]);
});

test("an exact expected value or a printed normal form is computed before the assumptions are checked, and a pattern or a value form after", async t => {
  const { result } = await checkProgram(t, `import unat;
use unat;
def mixed := TruncateIntro(U0, UNat, 2 * 256);
evaluate mixed expecting mixed;
evaluate mixed expecting !_;
print(evaluate(!!mixed));
print(witness(mixed));
print(evaluate(mixed));
print(evaluate(!mixed));`, { module });
  assert.deepEqual(result.gaps.filter(gap => gap.directive).map(gap => gap.code), ["K344", "E324", "K344", "K344", "E324", "E324"]);
});

test("a typed pattern's lazy comparison asks a part shared under other binders once", async t => {
  // b0 is Unit only after a step, so no two types below are alpha-equal,
  // and each repeats its predecessor, under the binder of its own pair.
  const lines = ["def a0 := Unit;", "def b0 := (fun (X : U0) => X)(Unit);"];
  for (let level = 1; level <= 18; level++) lines.push(`def a${level} := a${level - 1} and a${level - 1};`,
    `def b${level} := b${level - 1} and b${level - 1};`);
  lines.push("def identity_ : a18 -> a18 := fun (x : a18) => x;", "evaluate identity_ expecting typed(b18 -> b18, _);");
  const program = new CubicalProgram(module, sourceReader());
  t.after(() => program.dispose());
  // The guide's questions, counted while the typed pattern asks them.
  const checker = program.checker, { differ } = checker;
  let calls = 0, asked = 0;
  checker.differ = function (...rest) {
    asked++;
    const driver = this.driver, { guide } = driver;
    driver.guide = function (...parts) { calls++; return guide.apply(this, parts); };
    try { return differ.apply(this, rest); }
    finally { driver.guide = guide; }
  };
  const result = await program.check(lines.join("\n"), "main");
  assert.deepEqual(result.gaps.map(gap => gap.reason), []);
  assert.equal(asked, 1);
  assert.ok(calls > 0 && calls < 1000, `${calls} questions to the guide`);
});

test("a typed pattern's lazy comparison stops at a depth, where conversion decides", async t => {
  // 4096 levels of succ on each side, built differently, so that nothing
  // short of comparing them all tells them equal.
  const { program } = await checkProgram(t, `import unat;
use unat;
def d := 2 * 256;
def o := 256 * 2;
def deep := d + d + d + d + d + d + d + d;
def other := o + o + o + o + o + o + o + o;
def deep_type := Unit or (deep = deep);
def other_type := Unit or (other = other);
def void_type := Void or (other = other);`, { module });
  const checker = program.checker, at = name => ({ tag: "DefRef", name: `main__${name}` });
  assert.equal(checker.differ(at("deep"), at("other")), false);
  assert.equal(checker.differ(at("deep_type"), at("other_type")), false);
  // A difference beside the deep parts is still found.
  assert.equal(checker.differ(at("deep_type"), at("void_type")), true);
});

test("a part the depth cut short is asked again where it is met with more depth left", async t => {
  // a0 and b0 differ one part down. Met first at the bottom of a499 and
  // b499, past the depth, they are unknown there, and differ beside them.
  // So do c0 and d0, which hold a0 and b0, met first below c497 and d497,
  // where only the unknown kept for a0 and b0 is reused.
  const lines = ["import unat;", "use unat;", "def deep := 2 * 256;", "def a0 := Unit or (deep = deep);", "def b0 := Void or (deep = deep);",
    "def c0 := a0 or Unit;", "def d0 := b0 or Unit;"];
  for (let level = 1; level < 500; level++) lines.push(`def a${level} := Unit or a${level - 1};`, `def b${level} := Unit or b${level - 1};`,
    `def c${level} := Unit or c${level - 1};`, `def d${level} := Unit or d${level - 1};`);
  lines.push("def a_ := a499 or a0;", "def b_ := b499 or b0;", "def c_ := (a498 or c497) or c0;", "def d_ := (b498 or d497) or d0;");
  const { program, result } = await checkProgram(t, lines.join("\n"), { module });
  assert.ok(result.outputs.length > 2000 && result.outputs.every(output => output.verified));
  const at = name => ({ tag: "DefRef", name: `main__${name}` });
  assert.equal(program.checker.differ(at("a_"), at("b_")), true);
  assert.equal(program.checker.differ(at("c_"), at("d_")), true);
});

test("a constructor is shown without its type's parameters, and a type as it is, however large", async t => {
  // Tag's parameter, as the kernel holds it, is twelve nested applications
  // of twice to succ, unreduced: a display that reduced it would build
  // 4096 applications of succ.
  const twice = "(fun (f : UNat -> UNat) => fun (x : UNat) => f(f(x)))";
  let parameter = "succ";
  for (let i = 0; i < 12; i++) parameter = `${twice}(${parameter})`;
  const { result } = await checkProgram(t, `import unat;
use unat;
inductive Tag(f : UNat -> UNat) : U0 {
  tag;
}
def tagged : Tag(${parameter}) := tag;
evaluate tagged expecting !_;
evaluate tagged expecting typed(Unit, _);`, { module });
  assert.deepEqual(result.evaluations.map(evaluation => evaluation.value), ["tag"]);
  // Nor is its type, where a typed pattern names another.
  assert.deepEqual(result.gaps.map(gap => gap.code), ["E483"]);
  assert.match(result.gaps[0].reason, /a part of type Tag\(\(fun \(f : UNat -> UNat, x : UNat\) => f\(f\(x\)\)\)/);
});

test("a glue value is shown as the introduction it is, on an empty or a false face", async t => {
  const { result } = await checkProgram(t, `import contractible_maps;
evaluate typed(Glue(Unit), glue(tt)) expecting !_;
evaluate typed(Glue(Unit, face_when(0, Unit, id_contr_equiv(U0, Unit))), glue(tt, face_when(0, tt))) expecting !_;`, { module });
  assert.deepEqual(result.gaps.map(gap => gap.reason), []);
  // The kernel keeps no part on a false face.
  assert.deepEqual(result.evaluations.map(evaluation => evaluation.value), ["glue(<unevaluated>)", "glue(<unevaluated>)"]);
});

test("an ignored component whose weak head fails does not fail the pattern", async t => {
  // The prime of euclid(4) has two successor heads, and its third is too deep
  // to compute (K344): any query of the ignored part, however indirect,
  // fails the evaluation.
  const { result } = await checkProgram(t, `import euclid;
use unat;
def pred(n : UNat) : UNat := match n {
  zero => zero;
  succ(k) => k;
};
def value : UNat and UNat := (1, pred(pred(euclid(4).1)));
evaluate value expecting (1, _);
evaluate value expecting (!_, _);
evaluate value expecting (_, !_);
`, { module });
  assert.deepEqual(result.evaluations.map(evaluation => evaluation.value), ["(1, <unevaluated>)", "(succ(<unevaluated>), <unevaluated>)"]);
  assert.deepEqual(result.gaps.map(gap => gap.code), ["K344"]);
});

test("an unobserved part is asked nothing: no query reaches a pair's ignored component", async t => {
  for (const pattern of ["(7, _)", "(!_, _)", "!(7, _)"]) {
    const { program, evaluations, asked } = recordedProgram(t);
    const result = await program.check(`import euclid;\nuse unat;\ndef value := euclid(3);\nevaluate value expecting ${pattern};`, "main");
    assert.deepEqual(result.gaps.map(gap => gap.reason), [], pattern);
    const [evaluation] = evaluations.filter(item => item.name === "main__value");
    // The evaluated term's weak head is the pair; its second component is
    // never asked for, and the whole term is never normalized.
    const first = asked.findIndex(item => item.query === "head" && item.handle === evaluation.handle);
    const pair = program.kernel.node(asked[first].result);
    assert.equal(pair.kind, "Pair", pattern);
    const ignored = pair.children[2];
    assert.deepEqual(asked.slice(first).filter(item => item.handle === ignored || item.query === "normalize" && item.handle === evaluation.handle), [], pattern);
    assert.equal(evaluation.normalized, false, pattern);
  }
});

test("print(evaluate(e)) shows the value form, !e the weak head as it is, !!e the normal form and !!!e the full one", async t => {
  const { result } = await checkProgram(t, `import unat;
use unat;
def double(n : UNat) := n + n;
def pair_ : UNat and (UNat -> UNat) := (double(3), double);
def far : UNat and UNat := (2 * 255, 2 * 255);
print(evaluate(pair_));
print(evaluate(!pair_));
print(evaluate(!!pair_));
print(evaluate(!!!pair_));
print(evaluate(UNat));
print(evaluate(refl(1)));
print(evaluate(fun (n : UNat) => succ(n)));
print(evaluate(!(fun (n : UNat) => succ(n))));
print(evaluate(fun (n : UNat) => induction n return UNat { zero => 0; succ h => succ(h); }));
print(evaluate(far));
print(evaluate(!!far));
`, { module });
  assert.deepEqual(result.prints.map(print => print.text), [
    "(6, <fun>)",
    "(double(3), double)",
    // The data computes; the function stays named, its value no data, and
    // only !!! unfolds it.
    "(6, double)",
    "(6, fun (n : UNat) => induction n return UNat { zero => n; succ h => succ(h); })",
    "<type>",
    "<path>",
    // Eta makes the successor function the constructor, whose value it is,
    // and an induction on its variable the eliminator alone, a function.
    "succ",
    "succ",
    "<fun>",
    // Each weak head of the numerals is shallow, so the value form reaches
    // a pair whose normal form is too deep to build.
    "(510, 510)",
  ]);
  assert.deepEqual(result.gaps.map(gap => gap.code), ["K344"]);
});

test("the printer shows every part the value form computed, in the order it shows them", async t => {
  const { program } = await checkProgram(t, `import unat;
use unat;
inductive Tree : U0 {
  leaf;
  node(l : Tree, datum : UNat, r : Tree);
}
def grow(n : UNat) : Tree := match n {
  zero => leaf;
  succ(k) => node(grow(k), 0, grow(k));
};
def wide := node(grow(12), 7, grow(12));`, { module });
  const { checker } = program, kernel = checker.kernel;
  const at = { head: handle => checker.derivedHead(handle), spine: handle => kernel.spine(handle),
    constructor: handle => checker.shownConstructor(handle),
    fieldOrder: constructor => checker.displayNames[constructor.sort.signature]?.constructors?.[constructor.index]?.order ?? null };
  const { expression } = checker.evaluated({ tag: "DefRef", name: "main__wide" });
  const form = valueForm(expression, at, null);
  // 2 * 4096 nodes are past the budget: the printer's own limit cuts
  // nothing the walk computed, so lifting it changes nothing.
  const shown = checker.printed(form, Infinity, printedNodes);
  assert.equal(shown, checker.printed(form, Infinity, Infinity));
  assert.match(shown, /^node\(node\(node\(/);
  // The fields are computed in source order: the left subtree spends the
  // budget, so the datum after it is not computed, though the kernel holds
  // it first.
  assert.match(shown, /, …, …\)$/);
});

test("a field the printer does not reach is not computed, though the kernel holds it first", async t => {
  const { result } = await checkProgram(t, `import euclid;
use unat;
inductive Tree : U0 {
  leaf;
  node(l : Tree, datum : UNat, r : Tree);
}
def grow(n : UNat) : Tree := match n {
  zero => leaf;
  succ(k) => node(grow(k), 0, grow(k));
};
def far : (Tree and Tree) and UNat := ((grow(10), grow(9)), euclid(4).1);
print(evaluate(node(grow(12), euclid(4).1, leaf)));
print(evaluate(far));`, { module, options: { runtimeEvaluation: false } });
  // euclid(4)'s prime has a weak head too deep for the kernel to build
  // (K344), and neither print reaches it.
  assert.deepEqual(result.gaps.map(gap => gap.reason), []);
  assert.equal(result.prints.length, 2);
});

test("print(evaluate(!e)) shows the weak head as the kernel leaves it, reducing nothing for display", async t => {
  const { result } = await checkProgram(t, `import unat;
use unat;
def p : UNat and UNat := ((fun (x : UNat) => succ(x))(2), 0);
print(evaluate(!p));
print(evaluate(p));`, { module });
  assert.deepEqual(result.prints.map(print => print.text), ["((fun (x : UNat) => succ(x))(2), 0)", "(3, 0)"]);
});

test("the value form stops exactly where the printer's 4,000 nodes end", async t => {
  // A row of twenty units costs 22 nodes as the printer counts them: wide
  // applied, which is two, and twenty tt; with its cons, two more, 24. A head
  // is computed while two of the 4,000 remain: 166 rows cost 3,984, the
  // 167th's cons and wide 4 more, and 11 of its units bring the 16 left to
  // 1. Its other nine units and the list's tail are shown as …, uncomputed.
  // The list nests about 190 levels, short of the depth of 512.
  const { result } = await checkProgram(t, `import lists;
use unat;
inductive Wide : U0 {
  wide(a1 : Unit, a2 : Unit, a3 : Unit, a4 : Unit, a5 : Unit, a6 : Unit, a7 : Unit, a8 : Unit, a9 : Unit, a10 : Unit, a11 : Unit, a12 : Unit, a13 : Unit, a14 : Unit, a15 : Unit, a16 : Unit, a17 : Unit, a18 : Unit, a19 : Unit, a20 : Unit);
}
def rows(n : UNat) : List(U0, Wide) := match n {
  zero => nil;
  succ(k) => cons(wide(tt, tt, tt, tt, tt, tt, tt, tt, tt, tt, tt, tt, tt, tt, tt, tt, tt, tt, tt, tt), rows(k));
};
print(evaluate(rows(8 * 250)));`, { module });
  assert.deepEqual(result.gaps.map(gap => gap.reason), []);
  const text = result.prints[0].text;
  assert.equal(text.match(/\btt\b/g).length, 166 * 20 + 11);
  assert.equal(text.match(/…/g).length, 10);
  assert.match(text, /, tt, …, …, …, …, …, …, …, …, …\), …\)/);
});

test("a glue value's value form is the introduction, with its base computed", async t => {
  const { result } = await checkProgram(t, `import contractible_maps;
import unat;
use unat;
def g : Glue(UNat) := glue(1 + 1);
print(evaluate(g));
print(evaluate(!g));
print(evaluate(!!g));`, { module });
  assert.deepEqual(result.gaps.map(gap => gap.reason), []);
  assert.deepEqual(result.prints.map(print => print.text), ["glue(2)", "glue(1 + 1)", "glue(2)"]);
});

// Each head a value form computes, an observation of the runtime or a head
// query of the kernel's, spends a query of its print's fuel.
const printFuel = result => result.directiveFuel.find(directive => directive.kind === "print").searchFuel.queries;
test("the value form computes no more heads than the printer shows", async t => {
  const spent = [];
  for (const runtimeEvaluation of [true, false]) {
    const { result } = await checkProgram(t, `import lists;
use unat;
def hundreds(n : UNat) : List(U0, UNat) := match n {
  zero => nil;
  succ(k) => cons(100, hundreds(k));
};
print(evaluate(hundreds(250)));`, { module, options: { runtimeEvaluation } });
    assert.deepEqual(result.gaps.map(gap => gap.reason), []);
    assert.equal(result.prints[0].valueForm.by, runtimeEvaluation ? "runtime" : "kernel");
    // 250 elements of 102 heads each are past the budget of 4,000 heads.
    spent.push(printFuel(result));
    assert.ok(spent.at(-1) <= 4100, `the walk asked ${spent.at(-1)} queries`);
    assert.match(result.prints[0].text, /^cons\(100, cons\(100, /);
  }
  // The runtime's walk asks the type's weak head first, which decides
  // whether the runtime is asked at all.
  assert.equal(spent[0], spent[1] + 1);
});

test("the value form shows no part deeper than the kernel's terms, however deep the value", async t => {
  const texts = [];
  for (const runtimeEvaluation of [true, false]) {
    const { result } = await checkProgram(t, `import unat;
use unat;
def d := 2 * 256;
def deep := d + d + d + d + d + d + d + d;
print(evaluate(deep));`, { module, options: { runtimeEvaluation } });
    assert.deepEqual(result.gaps.map(gap => gap.reason), []);
    assert.equal(result.prints[0].valueForm.by, runtimeEvaluation ? "runtime" : "kernel");
    // 4096 levels of succ: the walk keeps its own stack, and computes heads
    // only to 512 levels, where the kernel's own terms end.
    texts.push(result.prints[0].text);
    assert.match(texts.at(-1), /^succ\(succ\(succ\(/);
    assert.ok(printFuel(result) <= 600, `the walk asked ${printFuel(result)} queries`);
  }
  assert.equal(texts[0], texts[1]);
});

test("the REPL reads the marks after evaluate and before a term alone", async () => {
  const { ReplSession } = await import("../web/repl-session.mjs");
  const program = new CubicalProgram(module, sourceReader());
  try {
    const session = new ReplSession(program);
    await session.run("import unat; use unat; let f := fun (n : UNat) => n + 1;");
    const shown = async entry => (await session.run(entry)).map(result => result.text).join("\n");
    assert.equal(await shown("evaluate f;"), "<fun>");
    assert.equal(await shown("f;"), "<fun>");
    // A lambda is its own weak head, shown as it is.
    assert.equal(await shown("evaluate !f;"), "fun (n : UNat) => n + 1");
    assert.equal(await shown("evaluate!f;"), "fun (n : UNat) => n + 1");
    // The term asked for is unfolded; n + 1, stuck on n, stays as written
    // under !!, and !!! unfolds it.
    assert.equal(await shown("evaluate !!f;"), "fun (n : UNat) => n + 1");
    assert.equal(await shown("!!f;"), await shown("evaluate !!f;"));
    assert.equal(await shown("evaluate !!!f;"), "fun (n : UNat) => induction n return UNat { zero => 1; succ h => succ(h); }");
    assert.equal(await shown("!!!f;"), await shown("evaluate !!!f;"));
    assert.equal(await shown("evaluate f(2);"), "3");
  } finally { program.dispose(); }
});

test("an unobserved part is not computed: the queries a pattern asks cost what it observes", async t => {
  const ticks = async source => {
    const { program, result } = await checkProgram(t, `import euclid;\nuse unat;\ndef value := euclid(3);\n${source}`, { module });
    assert.deepEqual(result.gaps.map(gap => gap.reason), [], source);
    return Number(program.kernel.work().querySteps);
  };
  const none = await ticks(""), head = await ticks("evaluate value expecting !_;");
  const prime = await ticks("evaluate value expecting (7, _);"), full = await ticks("evaluate value expecting !!!_;");
  assert.ok(head - none < 1000, `a weak head costs ${head - none} ticks`);
  assert.ok(prime - none < full - none, `the prime costs ${prime - none} ticks, the full normal form ${full - none}`);
});

test("normalize accepts the data parts of a derived handle's weak head, and only those", async t => {
  const { program } = await checkProgram(t, `import unat;\nuse unat;\ndef pair_ : UNat and (UNat -> UNat) := (2 + 1, fun (n : UNat) => n);`, { module });
  const checker = program.checker, kernel = checker.kernel;
  const { expression } = checker.checkSyntax({ tag: "DefRef", name: "main__pair_" }, null, new Map(), new Map());
  const [annotation, first, second] = kernel.node(kernel.head(expression)).children;
  // Before the head is asked for as a derived handle's, its parts are raw,
  // and the head of a raw handle records nothing.
  assert.throws(() => kernel.normalize(first), /Normalize a term or type an instruction derived/);
  checker.derivedHead(kernel.term("Pair", 0, annotation, first, second));
  assert.throws(() => kernel.normalize(first), /instruction derived/);
  assert.deepEqual(kernel.node(checker.derivedHead(expression)).children.slice(0, 3), [annotation, first, second]);
  assert.equal(checker.displayText(checker.normalForm(first), []), "unat.(3)");
  assert.equal(checker.normalForm(second).tag, "Lam");
  // Nothing below the data parts is admitted: not a lambda's domain or body,
  // even once the lambda's own head is asked, nor the parts of a part,
  // until that part's own head is asked.
  const lambda = kernel.node(checker.derivedHead(second));
  assert.equal(lambda.kind, "Lam");
  for (const handle of lambda.children.slice(0, 2)) assert.throws(() => kernel.normalize(handle), /instruction derived/);
  const [inner] = kernel.spine(kernel.head(first)).args;
  assert.throws(() => kernel.normalize(inner), /instruction derived/);
  assert.equal(kernel.spine(checker.derivedHead(first)).args[0], inner);
  assert.equal(checker.displayText(checker.normalForm(inner), []), "unat.(2)");
});

test("normalize accepts no annotation of a derived handle's weak head that was not derived already", async t => {
  const { program } = await checkProgram(t, `import unat;
use unat;
def nested_ : ((UNat and UNat) or Unit) and UNat := (left((1, 2)), 2 + 1);`, { module });
  const checker = program.checker, kernel = checker.kernel;
  const { expression, typeHandle } = checker.checkSyntax({ tag: "DefRef", name: "main__nested_" }, null, new Map(), new Map());
  // The outer pair's annotation is the checked type itself; the injection's,
  // the inner pair's and the constructor's sort are only parts of it.
  const pair = kernel.node(checker.derivedHead(expression));
  assert.equal(pair.children[0], typeHandle);
  const injection = kernel.node(checker.derivedHead(pair.children[1]));
  const inner = kernel.node(checker.derivedHead(injection.children[1]));
  const { root: constructor } = kernel.spine(checker.derivedHead(pair.children[2]));
  assert.deepEqual([injection.kind, inner.kind, constructor.kind], ["Inl", "Pair", "Con"]);
  for (const annotation of [injection.children[0], inner.children[0], constructor.children[0]])
    assert.throws(() => kernel.normalize(annotation), /instruction derived/);
  assert.equal(checker.displayText(checker.normalForm(inner.children[1]), []), "unat.(1)");
});

test("the head of a derived path or level lambda admits nothing under its binder", async t => {
  const { program } = await checkProgram(t, `import unat;
use unat;
def path_ : 1 + 1 = 2 := path i => 2;
def level_(U < UU0, A : U, x : A) : A := x;`, { module });
  const checker = program.checker, kernel = checker.kernel;
  for (const [name, kind] of [["main__path_", "PLam"], ["main__level_", "LLam"]]) {
    const { expression } = checker.checkSyntax({ tag: "DefRef", name }, null, new Map(), new Map());
    const head = kernel.node(checker.derivedHead(expression));
    assert.equal(head.kind, kind, name);
    for (const handle of head.children.filter(Boolean)) assert.throws(() => kernel.normalize(handle), /instruction derived/, name);
  }
});

test("a warning in a failed evaluation is written above that evaluation, and an error located inside it above its line", async t => {
  const source = `import unat;
use unat;

def pairs : UNat and UNat := (3, 4);

evaluate pairs expecting !(
  2 * 255,
  _
);
`;
  const { result } = await checkProgram(t, source, { module });
  assert.deepEqual(reported(source, result, "main").map(({ line, label, text }) => [line, label, text.slice(0, 4)]),
    [[5, "Warning", "W709"], [6, "Error", "K344"]]);
});

test("demand marks format tightly and lint what asks for nothing more", () => {
  const source = "evaluate  !! e expecting ( ! _ , cons( !!_ , ! (1, _) ) ) ;\n";
  const formatted = formatCubist(source);
  assert.equal(formatted, "evaluate !!e expecting (!_, cons(!!_, !(1, _)));\n");
  assert.equal(formatCubist(formatted), formatted);
  const full = "evaluate  !!! e expecting ( !!! _ , ( !! _ , _ ) ) ;\n";
  assert.equal(formatCubist(full), "evaluate !!!e expecting (!!!_, !!_, _);\n");
  // Marks in a row are refused, so that no spacing turns ! !!_ into !!!_.
  for (const written of ["evaluate tt expecting ! !!_;", "evaluate tt expecting (!  !!_, !! !_);"])
    assert.throws(() => formatCubist(written), /Two demand marks in a row/, written);
  // A name or a call may be a constructor, which computes only a weak head,
  // so !! before one is not redundant, unless it is a builtin's; typed(T, p)
  // asks what p asks.
  assert.deepEqual(lint("evaluate v expecting (_, !!tok, !!succ(2), !!(1, 2), !typed(Unit, _), !!left(tt));"), []);
  assert.deepEqual(lint("evaluate v expecting (_, !!tt, !!Unit, !!refl(tt), !!U0);").map(warning => warning.code),
    ["W710", "W710", "W710", "W710"]);
  assert.deepEqual(lint("evaluate v expecting (!typed(Unit, tt), !!typed(UNat, 4), !!nat.(2 + 3), _);").map(warning => warning.code),
    ["W709", "W710", "W710"]);
  // Without a hole, removing the marks would compare the value whole: they
  // are not reported.
  assert.deepEqual(lint("evaluate v expecting !tok; evaluate v expecting (!!3, !!4); evaluate !!v expecting 3;"), []);
  assert.deepEqual(lint(formatted).map(warning => warning.code), ["W708", "W708", "W708"]);
  assert.deepEqual(lint("evaluate e expecting (!5, !!3, !!(4, !_), !_, !!_, !typed(Unit, _));").map(warning => warning.code),
    ["W709", "W710", "W708"]);
  // Under !!!, every mark asks for nothing more; under !!, a !!! asks for
  // more, which the checker refuses (E486), and !!! before an expression
  // asks for its full normal form.
  assert.deepEqual(lint("evaluate e expecting !!!(!!_, !_, _); evaluate e expecting (!!(!!!_, _), !!!3, _);").map(warning => warning.code),
    ["W708", "W708"]);
  assert.match(lint("evaluate e expecting !!!(!!_, _);")[0].message, /it is under !!!, which normalizes its part/);
  // Nor is a mark of a refused combination reported: removing the inner !!!
  // or the !! of !!!(!!(!!!_), _) would make the refused entry check.
  assert.deepEqual(lint("evaluate e expecting !!!(!!(!!!_), _); evaluate e expecting (!!_, !!(tt, !!!_));"), []);
});

// One closed example of every construct with a term to evaluate, and its
// weak head on main, from the demand marks note. Each evaluates under !_,
// shown as its recorded head, under !!_, and printed, as its value form,
// except the assumptions, which evaluation refuses. Three examples whose
// full normal forms are slow are not evaluated under !!!_: A46b's costs
// about 30 seconds, and since B8's direct proof of prop_type_is_set the
// literals B62 and B63 about 11.6M ticks and 5 to 10 seconds each. The DM5
// report (docs/roadmaps/historical/evaluation-demand-marks/report.md)
// records that they complete. Their folded normal forms, under !!_, are
// quick. Each is printed twice: its value form observed by the runtime
// (web/cubical-runtime.mjs), which reports the demand it does not support
// and leaves it to the kernel's head queries, and by those queries alone,
// which must show the same value.
const corpus = JSON.parse(readFileSync(new URL("../docs/roadmaps/historical/evaluation-demand-marks/constructs.json", import.meta.url), "utf8"));
const slowNormalForms = new Set(["A46b-theory-labelled-parent", "B62-rational-literal", "B63-decimal-literal"]);
const typeKinds = new Set(["U", "Pi", "Sigma", "Path", "Sum", "Unit", "Void", "Glue", "Sort", "LPi"]);
const shownHead = whnf => {
  const [, kind, count = 0] = /^(\w+)(?: applied to (\d+))?$/.exec(whnf);
  if (kind === "Con") return shown => !shown.startsWith("<") && (shown.match(/<unevaluated>/g) ?? []).length === Number(count);
  const expected = { Lam: "<fun>", PLam: "<path>", LLam: "<level fun>", HComp: "<composition>", Pair: "(<unevaluated>, <unevaluated>)",
    Inl: "left(<unevaluated>)", Inr: "right(<unevaluated>)", Point: "tt" }[kind] ?? (typeKinds.has(kind) ? "<type>" : null);
  assert.ok(expected, `no shown head for ${whnf}`);
  return shown => shown === expected;
};
// The value form of a term with that weak head: a marker for a head that is
// no data, and otherwise the data with its parts computed.
const printedHead = whnf => {
  const [, kind] = /^(\w+)/.exec(whnf);
  if (kind === "Con") return shown => !shown.startsWith("<");
  if (kind === "Pair") return shown => shown.startsWith("(");
  if (kind === "Inl" || kind === "Inr") return shown => shown.startsWith(kind === "Inl" ? "left(" : "right(");
  const expected = { Point: "tt", Lam: "<fun>", PLam: "<path>", LLam: "<level fun>", HComp: "<composition>" }[kind]
    ?? (typeKinds.has(kind) ? "<type>" : null);
  return shown => shown === expected;
};
for (const setup of Object.keys(corpus.setups)) {
  const items = corpus.constructs.filter(item => item.setup === setup);
  if (!items.length) continue;
  test(`every construct of setup ${setup} evaluates under !_, !!_ and !!!_ and prints`, async t => {
    // Each directive's line names its construct.
    const lines = [corpus.setups[setup], ""], at = new Map();
    items.forEach((item, index) => {
      lines.push(`def probe_${index} := ${item.term};`);
      for (const mark of slowNormalForms.has(item.id) ? ["!_", "!!_"] : ["!_", "!!_", "!!!_"]) {
        at.set(lines.join("\n").split("\n").length + 1, [item, mark]);
        lines.push(`evaluate probe_${index} expecting ${mark};`);
      }
      at.set(lines.join("\n").split("\n").length + 1, [item, "print"]);
      lines.push(`print(evaluate(probe_${index}));`);
      at.set(lines.join("\n").split("\n").length + 1, [item, "kernel print"]);
      lines.push(`print(evaluate(probe_${index}));`);
    });
    const { program, evaluations } = recordedProgram(t), valueFormOf = Translator.prototype.valueFormOf;
    // Of each pair of value forms, the first may ask the runtime and the
    // second is the kernel's queries' alone.
    let turn = 0;
    Translator.prototype.valueFormOf = function (...args) {
      this.checker.runtimeEvaluation = turn++ % 2 === 0;
      try { return valueFormOf.apply(this, args); } finally { this.checker.runtimeEvaluation = true; }
    };
    let result;
    try { result = await program.check(lines.join("\n"), "main"); }
    finally { Translator.prototype.valueFormOf = valueFormOf; }
    const outcome = new Map([...result.evaluations.map(evaluation => [evaluation.start, evaluation.value]),
      ...result.prints.map(print => [print.start, print.text]),
      ...result.gaps.filter(gap => gap.directive).map(gap => [gap.declarationStart, { refused: gap.code }])]);
    const source = lines.join("\n"), lineOf = offset => source.slice(0, offset).split("\n").length;
    const outcomes = new Map([...outcome].map(([start, value]) => [lineOf(start), value]));
    const computed = new Map(result.prints.map(print => [lineOf(print.start), print.valueForm]));
    // Each directive checks its probe once for evaluation, in order: whether
    // it normalized the whole term is the directive's demand.
    const checked = new Map(items.map((_, index) => [index, evaluations.filter(evaluation => evaluation.name === `main__probe_${index}`)]));
    for (const [line, [item, mark]] of at) {
      const value = outcomes.get(line), index = items.indexOf(item), position = [...at.values()].filter(([other]) => other === item)
        .findIndex(([, other]) => other === mark);
      const evaluation = checked.get(index)[position], wholeNormalized = evaluation?.normalized;
      if (item.refused) {
        assert.deepEqual(value, { refused: item.refused }, `${item.id} ${mark}`);
        assert.notEqual(wholeNormalized, true, `${item.id} ${mark}: refused before computing`);
        continue;
      }
      if (mark === "kernel print") {
        // The runtime's value form, or its fallback, is the kernel's.
        const runtime = [...at].find(([, [other, kind]]) => other === item && kind === "print")[0];
        assert.equal(outcomes.get(runtime), value, `${item.id}: the runtime's value form is the kernel's`);
        assert.equal(computed.get(line).by, "kernel", item.id);
        const by = computed.get(runtime);
        if (by.by === "runtime") valueForms.runtime++;
        else valueForms.unsupported[by.unsupported] = (valueForms.unsupported[by.unsupported] ?? 0) + 1;
        // A fallback decided from the type takes no snapshot.
        if (by.by === "kernel" && !by.runtime) valueForms.early++;
        continue;
      }
      assert.equal(typeof value, "string", `${item.id} ${mark}: ${JSON.stringify(value)}`);
      const normalizes = mark === "!!_" || mark === "!!!_";
      assert.equal(wholeNormalized, normalizes, `${item.id} ${mark}: the whole term ${normalizes ? "is" : "is not"} normalized`);
      if (normalizes) assert.equal(evaluation.folded, mark === "!!_", `${item.id} ${mark}: ${mark === "!!_" ? "folded" : "full"}`);
      if (mark === "!_") {
        assert.ok(shownHead(item.whnf)(value), `${item.id}: ${value} is not ${item.whnf}`);
        // A constructor shown is the one at the kernel's own weak head.
        if (item.whnf.startsWith("Con")) {
          let constructor = evaluation.displayed;
          while (constructor?.tag === "App") constructor = constructor.fn;
          assert.equal(constructor?.tag, "Con", `${item.id}: ${value} shows a constructor`);
          const { root } = evaluation, identity = con => [con?.index, con?.name, con?.sort?.signature];
          assert.deepEqual(identity(constructor), identity(root), `${item.id}: ${value} shows the kernel's constructor`);
        }
      } else if (mark === "!!_" || mark === "!!!_") {
        // What !!_ and !!!_ show is the normal form the kernel computed,
        // folded or full, up to the names of bound variables.
        assert.doesNotMatch(value, /<unevaluated>|<fun>|<type>/, `${item.id}: a normal form`);
        // Compared as graphs: a folded normal form can share a part, such as
        // a theory's record, that a tree would repeat many times.
        assert.equal(sharedNormalDigest(evaluation.shown).digest, sharedNormalDigest(evaluation.normal).digest, `${item.id}: the kernel's normal form is shown`);
      }
      else {
        // The value form computes every part it shows: none is unevaluated,
        // and its head is the kernel's, a constructor the one at its weak head.
        assert.doesNotMatch(value, /<unevaluated>|<neutral>/, `${item.id}: a value form`);
        assert.ok(printedHead(item.whnf)(value), `${item.id}: ${value} is not the value form of ${item.whnf}`);
        if (item.whnf.startsWith("Con")) {
          let constructor = evaluation.displayed;
          while (constructor?.tag === "App") constructor = constructor.fn;
          const { root } = evaluation, identity = con => [con?.index, con?.name, con?.sort?.signature];
          assert.deepEqual(identity(constructor), identity(root), `${item.id}: ${value} shows the kernel's constructor`);
        }
        // Where it marks nothing, it is the normal form, folded and full alike.
        const normal = outcomes.get([...at].find(([, [other, kind]]) => other === item && kind === "!!_")?.[0]);
        if (!/[<…]/.test(value) && typeof normal === "string" && !normal.includes("…"))
          assert.equal(value, normal, `${item.id}: the value form of data is its normal form`);
      }
    }
  });
}
// What computed the value forms above, the runtime or, for the demand it
// reports unsupported, the kernel's head queries. The four assumptions are
// refused before anything is computed. Of the fallbacks at a higher or
// truncated sort, 18 are values of such a sort, decided from their types
// before any snapshot, and 16 contain one.
const valueForms = { runtime: 0, unsupported: {}, early: 0 };
test("the runtime computes the value forms of the constructs on ordinary data", () => {
  assert.equal(valueForms.runtime, 135);
  assert.deepEqual(valueForms.unsupported, {
    "Higher and truncated data execution is not implemented.": 34,
    "Runtime execution of Comp is not implemented.": 17,
    "Runtime execution of PApp is not implemented.": 2,
    "Runtime η of a path abstraction is not implemented.": 3,
    "Runtime execution of Glue is not implemented.": 1,
    "Runtime execution of Unglue is not implemented.": 1,
  });
  assert.equal(valueForms.early, 18);
});

// The acceptance report (docs/roadmaps/historical/evaluation-demand-marks/
// report.md) compares normal forms by sharedNormalDigest, which reads each
// shared object of a decoding once for each way its free names are bound, as
// normal forms too large to walk as trees need. It must tell terms apart
// exactly as normalDigest does: up to the names of bound variables and
// dimensions and the slots the kernel gives them, and no further, across
// programs as well as within one.
const digested = (program, value) => {
  const decoded = program.checker.syntax.decode(value, program.checker.dimensions);
  return { shared: sharedNormalDigest(decoded).digest, decoded: normalDigest(decoded) };
};
const definitionValue = (program, name, owner = "main") => program.kernel.definition(program.kernel.definitions.get(`${owner}__${name}`)).value;
test("the report's digest tells terms apart as the baseline's digest of their decodings does", async t => {
  const square = "fun (A : U0, x : A, s : refl(x) = refl(x)) => typed(refl(x) = refl(x), ";
  const terms = {
    first: "fun (x : UNat) => fun (y : UNat) => x",
    first_renamed: "fun (y : UNat) => fun (x : UNat) => y",
    second: "fun (x : UNat) => fun (y : UNat) => y",
    at_zero: "fun (A : U0, x : A, p : x = x) => p @ 0",
    at_one: "fun (A : U0, x : A, p : x = x) => p @ 1",
    lower: "fun (A : U0, x : A, p : x = x) => typed(x = x, path i => p @ (i & ~i))",
    lower_renamed: "fun (A : U0, x : A, p : x = x) => typed(x = x, path j => p @ (j & ~j))",
    upper: "fun (A : U0, x : A, p : x = x) => typed(x = x, path i => p @ (i | ~i))",
    rows: `${square}path i => path j => s @ i @ j)`,
    rows_renamed: `${square}path j => path i => s @ j @ i)`,
    columns: `${square}path i => path j => s @ j @ i)`,
    carry: "fun (A : U0, P : A -> U0, x : A, p : x = x, u : P(x)) => comp(fun (i : Interval) => P(p @ i), u)",
    carry_renamed: "fun (A : U0, P : A -> U0, x : A, p : x = x, u : P(x)) => comp(fun (j : Interval) => P(p @ j), u)",
    carry_back: "fun (A : U0, P : A -> U0, x : A, p : x = x, u : P(x)) => comp(fun (i : Interval) => P(p @ ~i), u)",
    two: "2",
    three: "3",
  };
  const source = `import unat;\nuse unat;\n${Object.entries(terms).map(([name, term]) => `def ${name} := ${term};`).join("\n")}`;
  const { program, verdicts } = await checkProgram(t, source, { module });
  const { syntax } = program.checker, digests = {};
  for (const name of Object.keys(terms)) {
    assert.equal(verdicts[name], true, name);
    digests[name] = digested(program, definitionValue(program, name));
  }
  // Terms as the kernel's normal forms may hold them, with their dimensions
  // in any slots, built directly: alike but for their slots, or different in
  // the binder a formula names, once in a part shared under both binders.
  const { kernel } = program, raw = (kind, payload, ...children) => kernel.term(kind, payload, ...children);
  const family = raw("Var", kernel.symbol("A")), path = raw("Var", kernel.symbol("p"));
  const at = slot => raw("PApp", syntax.formula([["d:1"]], "interval", new Map([["d", slot]])), path);
  const plam = (slot, body) => raw("PLam", slot, family, body);
  const built = {
    outer: plam(3, plam(5, at(3))),
    outer_moved: plam(5, plam(3, at(5))),
    inner: plam(3, plam(5, at(5))),
    shared_inner: plam(3, plam(5, raw("App", 0, at(3), plam(3, at(3))))),
    shared_outer: plam(3, plam(5, raw("App", 0, at(3), plam(4, at(3))))),
  };
  for (const [name, value] of Object.entries(built)) digests[name] = digested(program, value);
  const names = Object.keys(digests);
  for (const left of names) for (const right of names)
    assert.equal(digests[left].shared === digests[right].shared, digests[left].decoded === digests[right].decoded, `${left} and ${right}`);
  // The pairs that matter, so that the check is not vacuous.
  const same = (left, right) => digests[left].decoded === digests[right].decoded;
  for (const [left, right] of [["first", "first_renamed"], ["lower", "lower_renamed"], ["rows", "rows_renamed"], ["carry", "carry_renamed"],
    ["outer", "outer_moved"]])
    assert.ok(same(left, right), `${left} and ${right} are the same term`);
  for (const [left, right] of [["first", "second"], ["at_zero", "at_one"], ["lower", "upper"], ["rows", "columns"], ["carry", "carry_back"], ["two", "three"],
    ["outer", "inner"], ["shared_inner", "shared_outer"]])
    assert.ok(!same(left, right), `${left} and ${right} differ`);
});

// Every part decoding reads, in terms built directly as the kernel holds
// them: pairs that differ in that part alone, and pairs alike but for the
// names or slots of what a binder binds.
test("the report's digest reads every part decoding reads", async t => {
  const { program, verdicts } = await checkProgram(t, "import unat;\nuse unat;\ndef two := 2;\ndef three := 3;\ninductive Flag {\n  lit;\n  unlit;\n}\n", { module });
  assert.deepEqual([verdicts.two, verdicts.three], [true, true]);
  const { kernel, checker: { syntax } } = program, raw = (kind, payload, ...children) => kernel.term(kind, payload, ...children);
  const v = name => raw("Var", kernel.symbol(name)), level = value => raw("LConst", value);
  const face = (slot, bit = 1) => syntax.formula([[`d:${bit}`]], "face", new Map([["d", slot]]));
  const at = slot => raw("PApp", syntax.formula([["d:1"]], "interval", new Map([["d", slot]])), v("p"));
  const list = items => items.reduceRight((next, item) => raw("List", 0, item, next), 0);
  const flag = kernel.signatures.get("main__Flag").index, unat = kernel.signatures.get("unat__UNat").index;
  const sort = (signature, parameters, levels) => raw("Sort", signature, list(parameters), list(levels));
  const glue = (type, equiv, at) => raw("Glue", 0, v("a"), raw("GlueSystem", at, type, equiv, 0));
  const glueTerm = (as, term, at) => raw("GlueTerm", 0, as, v("b"), raw("Tube", at, term, 0));
  const tube = (at, term) => raw("Tube", at, term, 0), lambda = (name, body) => raw("Lam", kernel.symbol(name), v("A"), body);
  const formula = (clauses, outer, inner) => raw("PApp", syntax.formula(clauses, "interval", new Map([["d", outer], ["e", inner]])), v("p"));
  const both = (outer, inner) => formula([["d:1", "e:1"]], outer, inner), either = (outer, inner) => formula([["d:1"], ["e:1"]], outer, inner);
  const comp = term => raw("Comp", 3, v("A"), tube(face(4), term), v("b"));
  const faced = (kind, slot) => raw(kind, 3, v("A"), tube(face(slot), v("t")), v("b"));
  const levelLambda = (kind, bound, used) => raw(kind, kernel.symbol(bound), raw("LBound", 1), raw("U", 0, raw("Var", kernel.symbol(used))));
  const terms = {
    free_a: v("a"), free_b: v("b"),
    two: kernel.definitions.get("main__two"), three: kernel.definitions.get("main__three"),
    level_0: raw("U", 0, level(0)), level_1: raw("U", 0, level(1)),
    successor_1: raw("U", 0, raw("LSucc", 1, level(0))), successor_2: raw("U", 0, raw("LSucc", 2, level(0))),
    level_lambda: levelLambda("LLam", "l", "l"), level_lambda_renamed: levelLambda("LLam", "m", "m"), level_lambda_free: levelLambda("LLam", "l", "m"),
    level_pi: levelLambda("LPi", "l", "l"), level_pi_renamed: levelLambda("LPi", "m", "m"),
    glue: glue(v("t"), v("e"), face(3)), glue_type: glue(v("u"), v("e"), face(3)), glue_equiv: glue(v("t"), v("f"), face(3)), glue_face: glue(v("t"), v("e"), face(4)),
    glue_term: glueTerm(v("a"), v("t"), face(3)), glue_term_as: glueTerm(v("c"), v("t"), face(3)), glue_term_part: glueTerm(v("a"), v("u"), face(3)),
    glue_term_face: glueTerm(v("a"), v("t"), face(3, 0)),
    comp: raw("Comp", 3, v("A"), tube(face(4), at(3)), v("b")), comp_moved: raw("Comp", 5, v("A"), tube(face(4), at(5)), v("b")),
    comp_tube: raw("Comp", 3, v("A"), tube(face(4), at(4)), v("b")), comp_face: raw("Comp", 3, v("A"), tube(face(4, 0), at(3)), v("b")),
    hcomp: raw("HComp", 5, at(5), tube(face(4), at(5)), v("b")), hcomp_moved: raw("HComp", 6, at(5), tube(face(4), at(6)), v("b")),
    trans: raw("Trans", 3, at(3), tube(face(4), v("b")), v("b")), trans_moved: raw("Trans", 5, at(5), tube(face(4), v("b")), v("b")),
    trans_face: raw("Trans", 3, at(3), tube(face(4, 0), v("b")), v("b")),
    sort: sort(flag, [v("a")], [level(0)]), sort_signature: sort(unat, [v("a")], [level(0)]), sort_parameter: sort(flag, [v("b")], [level(0)]),
    sort_level: sort(flag, [v("a")], [level(1)]),
    // A variable is a parameter or a level: where the parameters end matters.
    sort_variables: sort(flag, [v("a"), v("b")], []), sort_split: sort(flag, [v("a")], [v("b")]),
    constructor: raw("Con", 0, sort(flag, [], [])), constructor_index: raw("Con", 1, sort(flag, [], [])),
    elim: raw("Elim", flag, v("m"), list([v("a"), v("b")])), elim_signature: raw("Elim", unat, v("m"), list([v("a"), v("b")])),
    elim_clause: raw("Elim", flag, v("m"), list([v("a"), v("c")])),
    // One variable node met under binders of its name and of others: the
    // inner x shadows the outer one, and z does not.
    shadowed: lambda("x", lambda("y", raw("App", 0, v("x"), lambda("x", v("x"))))),
    unshadowed: lambda("x", lambda("y", raw("App", 0, v("x"), lambda("z", v("x"))))),
    // What a binder does not bind: a lambda's domain, a path's endpoints, a
    // composition's and a transport's base.
    domain: raw("Lam", kernel.symbol("x"), v("x"), v("x")), domain_renamed: raw("Lam", kernel.symbol("y"), v("x"), v("y")),
    pi: raw("Pi", kernel.symbol("x"), v("A"), v("x")), pi_renamed: raw("Pi", kernel.symbol("y"), v("A"), v("y")),
    sigma: raw("Sigma", kernel.symbol("x"), v("A"), v("x")), sigma_renamed: raw("Sigma", kernel.symbol("y"), v("A"), v("y")),
    path_type: raw("Path", 3, at(3), at(3), v("a")), path_type_moved: raw("Path", 5, at(5), at(3), v("a")),
    path_family: raw("PLam", 3, at(3), v("a")), path_family_moved: raw("PLam", 5, at(5), v("a")),
    comp_base: raw("Comp", 3, v("A"), 0, at(3)), comp_base_moved: raw("Comp", 5, v("A"), 0, at(3)),
    trans_base: raw("Trans", 3, v("A"), tube(face(4), at(3)), at(3)), trans_base_moved: raw("Trans", 5, v("A"), tube(face(4), at(3)), at(3)),
    // A clause's literals in either order of their binders, and high slots.
    both: raw("PLam", 3, v("A"), raw("PLam", 5, v("A"), both(3, 5))), both_moved: raw("PLam", 5, v("A"), raw("PLam", 3, v("A"), both(3, 5))),
    either: raw("PLam", 3, v("A"), raw("PLam", 5, v("A"), either(3, 5))), either_moved: raw("PLam", 5, v("A"), raw("PLam", 3, v("A"), either(3, 5))),
    slot_33: at(33), slot_34: at(34), high: raw("PLam", 33, v("A"), at(33)), high_moved: raw("PLam", 40, v("A"), at(40)),
    // What decoding ignores: a path application's annotation, a level
    // binder's bound, a transport descriptor's term.
    annotated: raw("PApp", syntax.formula([["d:1"]], "interval", new Map([["d", 3]])), v("p"), v("T")),
    annotated_other: raw("PApp", syntax.formula([["d:1"]], "interval", new Map([["d", 3]])), v("p"), v("U")),
    level_bound: raw("LLam", kernel.symbol("l"), raw("LBound", 2), raw("U", 0, raw("Var", kernel.symbol("l")))),
    trans_descriptor: raw("Trans", 3, at(3), tube(face(4), v("c")), v("b")),
    // An outer binding read again after an inner binder of its name.
    restored: lambda("x", raw("App", 0, lambda("x", v("x")), v("x"))), restored_renamed: lambda("x", raw("App", 0, lambda("y", v("y")), v("x"))),
    restored_dimension: raw("PLam", 3, v("A"), raw("App", 0, raw("PLam", 3, v("A"), at(3)), at(3))),
    restored_dimension_renamed: raw("PLam", 3, v("A"), raw("App", 0, raw("PLam", 5, v("A"), at(5)), at(3))),
    // A system's faces are outside its binder.
    comp_face_outside: raw("Comp", 3, v("A"), tube(face(3), v("t")), v("b")), comp_face_outside_moved: raw("Comp", 5, v("A"), tube(face(3), v("t")), v("b")),
    hcomp_face_outside: raw("HComp", 3, v("A"), tube(face(3), v("t")), v("b")), hcomp_face_outside_moved: raw("HComp", 5, v("A"), tube(face(3), v("t")), v("b")),
    // One composition met under more binders, its tube naming an outer
    // variable or dimension, against one naming the inner binder's.
    shared_tube: lambda("x", raw("App", 0, comp(v("x")), lambda("y", comp(v("x"))))),
    shared_tube_inner: lambda("x", raw("App", 0, comp(v("x")), lambda("y", comp(v("y"))))),
    shared_tube_dimension: raw("PLam", 6, v("A"), raw("App", 0, comp(at(6)), raw("PLam", 7, v("A"), comp(at(6))))),
    shared_tube_dimension_inner: raw("PLam", 6, v("A"), raw("App", 0, comp(at(6)), raw("PLam", 7, v("A"), comp(at(7))))),
    // A closed part met at two depths, against a renamed copy below.
    closed_shared: raw("App", 0, lambda("x", v("x")), lambda("y", lambda("x", v("x")))),
    closed_copied: raw("App", 0, lambda("x", v("x")), lambda("y", lambda("z", v("z")))),
    closed_shared_dimension: raw("App", 0, raw("PLam", 3, v("A"), at(3)), raw("PLam", 5, v("A"), raw("PLam", 3, v("A"), at(3)))),
    closed_copied_dimension: raw("App", 0, raw("PLam", 3, v("A"), at(3)), raw("PLam", 5, v("A"), raw("PLam", 7, v("A"), at(7)))),
    // One variable or dimension met at one depth in two places, bound by the
    // inner binder in the second, against one bound by the outer binder.
    rebound: raw("App", 0, lambda("x", lambda("y", v("x"))), lambda("z", lambda("x", v("x")))),
    rebound_outer: raw("App", 0, lambda("x", lambda("y", v("x"))), lambda("z", lambda("w", v("z")))),
    rebound_dimension: raw("App", 0, raw("PLam", 3, v("A"), raw("PLam", 5, v("A"), at(3))), raw("PLam", 4, v("A"), raw("PLam", 3, v("A"), at(3)))),
    rebound_dimension_outer: raw("App", 0, raw("PLam", 3, v("A"), raw("PLam", 5, v("A"), at(3))), raw("PLam", 4, v("A"), raw("PLam", 6, v("A"), at(4)))),
    // A variable and a dimension of one name: neither's binder binds the other.
    homonym: raw("PLam", 3, v("A"), v("d3")), homonym_moved: raw("PLam", 4, v("A"), v("d3")),
    homonym_dimension: raw("PLam", 3, v("A"), lambda("d3", at(3))), homonym_dimension_renamed: raw("PLam", 3, v("A"), lambda("x", at(3))),
    // A system met under another binder, only its face naming a dimension.
    shared_face: raw("PLam", 6, v("A"), raw("App", 0, faced("Comp", 6), raw("PLam", 7, v("A"), faced("Comp", 6)))),
    shared_face_inner: raw("PLam", 6, v("A"), raw("App", 0, faced("Comp", 6), raw("PLam", 7, v("A"), faced("Comp", 7)))),
    shared_face_hcomp: raw("PLam", 6, v("A"), raw("App", 0, faced("HComp", 6), raw("PLam", 7, v("A"), faced("HComp", 6)))),
    shared_face_hcomp_inner: raw("PLam", 6, v("A"), raw("App", 0, faced("HComp", 6), raw("PLam", 7, v("A"), faced("HComp", 7)))),
    // Systems of two tubes.
    two_tubes: raw("Comp", 3, v("A"), raw("Tube", face(4), at(3), tube(face(5), v("t"))), v("b")),
    two_tubes_term: raw("Comp", 3, v("A"), raw("Tube", face(4), at(3), tube(face(5), v("u"))), v("b")),
    two_tubes_face: raw("Comp", 3, v("A"), raw("Tube", face(4), at(3), tube(face(6), v("t"))), v("b")),
    two_tubes_reversed: raw("Comp", 3, v("A"), raw("Tube", face(5), v("t"), tube(face(4), at(3))), v("b")),
    one_tube: raw("Comp", 3, v("A"), tube(face(4), at(3)), v("b")),
    one_tube_twice: raw("Comp", 3, v("A"), raw("Tube", face(4), at(3), tube(face(4), at(3))), v("b")),
    // A term of every other kind, for the changes below.
    application: raw("App", 0, v("f"), v("a")), first_of: raw("Fst", 0, v("q")), second_of: raw("Snd", 0, v("q")),
    pair: raw("Pair", 0, v("A"), v("a"), v("b")), abort: raw("Abort", 0, v("A"), v("i")), sum: raw("Sum", 0, v("A"), v("B")),
    left_of: raw("Inl", 0, v("A"), v("a")), right_of: raw("Inr", 0, v("A"), v("a")), sum_rec: raw("SumRec", 0, v("m"), v("l"), v("r"), v("s")),
    unit_rec: raw("UnitRec", 0, v("m"), v("o"), v("u")), unglue: raw("Unglue", 0, v("A"), v("g")), level_application: raw("LApp", 0, v("f"), level(2)),
    level_max: raw("U", 0, raw("LMax", 0, level(0), level(1))), level_tier: raw("U", 0, raw("LConst", (1 << 16) | 3)), level_bound_term: raw("LBound", 2),
    unit: raw("Unit", 0), point: raw("Point", 0), void: raw("Void", 0), path_of: raw("Path", 3, v("A"), v("a"), v("b")),
  };
  const digests = Object.fromEntries(Object.entries(terms).map(([name, value]) => [name, digested(program, value)]));
  // It counts every distinct object of the decoding, arrays among them.
  for (const [name, value] of Object.entries(terms)) {
    const decoded = syntax.decode(value, program.checker.dimensions);
    assert.equal(sharedNormalDigest(decoded).objects, distinctObjects(decoded), `${name} counts its objects`);
  }
  const names = Object.keys(digests);
  for (const left of names) for (const right of names)
    assert.equal(digests[left].shared === digests[right].shared, digests[left].decoded === digests[right].decoded, `${left} and ${right}`);
  const same = (left, right) => digests[left].decoded === digests[right].decoded;
  for (const [left, right] of [["level_lambda", "level_lambda_renamed"], ["level_pi", "level_pi_renamed"], ["comp", "comp_moved"],
    ["hcomp", "hcomp_moved"], ["trans", "trans_moved"], ["domain", "domain_renamed"], ["pi", "pi_renamed"], ["sigma", "sigma_renamed"],
    ["path_type", "path_type_moved"], ["path_family", "path_family_moved"], ["comp_base", "comp_base_moved"], ["trans_base", "trans_base_moved"],
    ["both", "both_moved"], ["either", "either_moved"], ["high", "high_moved"], ["restored", "restored_renamed"],
    ["restored_dimension", "restored_dimension_renamed"], ["comp_face_outside", "comp_face_outside_moved"], ["hcomp_face_outside", "hcomp_face_outside_moved"],
    ["closed_shared", "closed_copied"], ["closed_shared_dimension", "closed_copied_dimension"], ["homonym", "homonym_moved"],
    ["homonym_dimension", "homonym_dimension_renamed"], ["annotated", "annotated_other"], ["level_bound", "level_lambda"], ["trans_descriptor", "trans"]])
    assert.ok(same(left, right), `${left} and ${right} are the same term`);
  for (const [left, right] of [["free_a", "free_b"], ["two", "three"], ["level_0", "level_1"], ["successor_1", "successor_2"],
    ["level_lambda", "level_lambda_free"], ["level_lambda", "level_pi"], ["glue", "glue_type"], ["glue", "glue_equiv"], ["glue", "glue_face"],
    ["glue_term", "glue_term_as"], ["glue_term", "glue_term_part"], ["glue_term", "glue_term_face"], ["comp", "comp_tube"], ["comp", "comp_face"],
    ["trans", "trans_face"], ["sort", "sort_signature"], ["sort", "sort_parameter"], ["sort", "sort_level"], ["sort_variables", "sort_split"],
    ["constructor", "constructor_index"], ["elim", "elim_signature"], ["elim", "elim_clause"], ["shadowed", "unshadowed"], ["slot_33", "slot_34"],
    ["both", "either"], ["shared_tube", "shared_tube_inner"], ["shared_tube_dimension", "shared_tube_dimension_inner"],
    ["shared_face", "shared_face_inner"], ["shared_face_hcomp", "shared_face_hcomp_inner"], ["two_tubes", "two_tubes_term"],
    ["two_tubes", "two_tubes_face"], ["two_tubes", "comp"], ["two_tubes", "two_tubes_reversed"], ["one_tube", "one_tube_twice"], ["rebound", "rebound_outer"],
    ["rebound_dimension", "rebound_dimension_outer"]])
    assert.ok(!same(left, right), `${left} and ${right} differ`);
  // Every term with one part of its decoding changed: each primitive to
  // another, each object to a fresh variable, each array one item shorter.
  // normalDigest reads every part, so a part the shared digest skipped
  // would make the two disagree on some change.
  let changes = 0;
  for (const [name, value] of Object.entries(terms)) {
    const decoded = syntax.decode(value, program.checker.dimensions), shared = sharedNormalDigest(decoded).digest, reference = normalDigest(decoded);
    for (const changed of oneChange(decoded)) {
      // A change no decoding gives, as a system that is no list, both refuse.
      const attempt = digest => { try { return digest(changed); } catch (error) { return error; } };
      const sharedChanged = attempt(value => sharedNormalDigest(value).digest), referenceChanged = attempt(normalDigest);
      assert.equal(sharedChanged instanceof Error, referenceChanged instanceof Error, `${name} changed: ${JSON.stringify(changed).slice(0, 200)}`);
      if (referenceChanged instanceof Error) continue;
      changes++;
      assert.equal(sharedChanged === shared, referenceChanged === reference, `${name} changed: ${JSON.stringify(changed).slice(0, 200)}`);
    }
  }
  assert.ok(changes > 1000, `${changes} changes`);
  // Every term beneath every context of up to two binders, each a
  // variable's or a dimension's, of a name the term holds or of a fresh
  // name: a name free in the term is bound by a binder of its kind and left
  // free by one of the other, the inner of two binders of a name shadows the
  // outer, and two contexts of one depth bind it at different distances.
  // Met once outside the context too, so that the copy outside fills the
  // memo first. And the copies beneath every context in one value, whose
  // digest is that of the value with nothing shared: the memo gives no part
  // the digest it has under another binding.
  let contexts = 0;
  for (const [name, value] of Object.entries(terms)) {
    const decoded = syntax.decode(value, program.checker.dimensions), { terms: termNames, dims: dimensionNames } = namesIn(decoded);
    const binders = [...new Set([...termNames, ...dimensionNames, "fresh′"])].flatMap(bound => [
      part => ({ tag: "Lam", name: bound, domain: { tag: "Var", name: "A" }, body: part }),
      part => ({ tag: "PLam", dim: bound, family: { tag: "Var", name: "A" }, body: part })]);
    const within = [part => part, ...binders, ...binders.flatMap(outer => binders.map(inner => part => outer(inner(part))))];
    agree(within.map(context => ({ tag: "App", fn: decoded, arg: context(decoded) })), `${name} met beneath binders`);
    const all = within.map(context => context(decoded));
    assert.equal(sharedNormalDigest(all).digest, sharedNormalDigest(unshared(all)).digest, `${name} met beneath every context at once`);
    contexts += within.length;
  }
  assert.ok(contexts > 10000, `${contexts} contexts`);
});

// The shared digests of some values tell them apart as the baseline's
// digests of them do.
function agree(values, label) {
  const sharedOf = new Map(), decodedOf = new Map();
  for (const value of values) {
    const shared = sharedNormalDigest(value).digest, decoded = normalDigest(value);
    assert.equal(sharedOf.get(decoded) ?? shared, shared, label);
    assert.equal(decodedOf.get(shared) ?? decoded, decoded, label);
    sharedOf.set(decoded, shared);
    decodedOf.set(shared, decoded);
  }
}

// A value with each of its objects copied wherever it occurs.
function unshared(value) {
  if (value === null || typeof value !== "object") return value;
  return Array.isArray(value) ? value.map(unshared) : Object.fromEntries(Object.entries(value).map(([key, item]) => [key, unshared(item)]));
}

// The number of distinct objects a value holds, itself and arrays among them.
function distinctObjects(value) {
  const seen = new Set(), pending = [value];
  while (pending.length) {
    const item = pending.pop();
    if (item === null || typeof item !== "object" || seen.has(item)) continue;
    seen.add(item);
    pending.push(...Object.values(item));
  }
  return seen.size;
}

// The names a decoded value holds anywhere: variables' and binders' names,
// and the dimensions its formulas and dimension binders name.
function namesIn(value) {
  const terms = new Set(), dims = new Set(), seen = new Set(), pending = [value];
  while (pending.length) {
    const item = pending.pop();
    if (item === null || typeof item !== "object" || seen.has(item)) continue;
    seen.add(item);
    if (Array.isArray(item) && item.length && item.every(Array.isArray))
      for (const clause of item) for (const literal of clause) dims.add(literal.slice(0, literal.lastIndexOf(":")));
    if (item.tag === "Var" || typeof item.name === "string") terms.add(item.name);
    if (typeof item.dim === "string") dims.add(item.dim);
    pending.push(...Object.values(item));
  }
  return { terms, dims };
}

// A value with one part changed, each way once.
function* oneChange(value) {
  if (value === null || typeof value !== "object") {
    yield typeof value === "number" ? value + 1000 : typeof value === "string" ? `${value}′` : value === undefined ? null : undefined;
    return;
  }
  yield { tag: "Var", name: "fresh′" };
  if (Array.isArray(value)) {
    if (value.length) yield value.slice(1);
    for (const [index, item] of value.entries()) for (const changed of oneChange(item)) yield value.map((other, at) => at === index ? changed : other);
  } else for (const [key, item] of Object.entries(value)) for (const changed of oneChange(item)) yield { ...value, [key]: changed };
}

// Both digests read any value decoding gives as it is: a field by its name
// and value, so values decoding does not give are compared alike too.
test("the report's digest compares plain values as normalDigest does", () => {
  const values = {
    field_a: { tag: "T", a: 1 }, field_b: { tag: "T", b: 1 }, field_null: { tag: "T", a: null }, field_undefined: { tag: "T", a: undefined },
    untagged: { a: 1 }, text: { tag: "T", a: "1" }, list: [1, 2], list_reversed: [2, 1], nested: [[1], 2],
    // Fields and roots that are no object, alike in their first characters,
    // or alike in their text but not their type.
    field_undefined_text: { tag: "T", a: "undefined" }, field_null_text: { tag: "T", a: "null" },
    text_1: "abcdefg1", text_2: "abcdefg2", number_0: 12345670, number_1: 12345671, number_text: "12345670",
    undefined_root: undefined, undefined_text: "undefined", null_root: null, null_text: "null", boolean: true, boolean_text: "true",
  };
  const digests = Object.fromEntries(Object.entries(values).map(([name, value]) => [name, { shared: sharedNormalDigest(value).digest, decoded: normalDigest(value) }]));
  for (const left of Object.keys(values)) for (const right of Object.keys(values)) {
    assert.equal(digests[left].shared === digests[right].shared, digests[left].decoded === digests[right].decoded, `${left} and ${right}`);
    if (left !== right) assert.notEqual(digests[left].decoded, digests[right].decoded, `${left} and ${right} differ`);
  }
});

// It reads each shared object once for each binding of its free names. In
// values of 2^22 paths, read through getters that count, a part is met
// beneath binders it does not mention, beneath binders of the names it binds
// itself, by a lambda, a path or a composition's system, and beneath binders
// of its free names at one distance and other depths, each of a variable and
// of a dimension. Each value is read in a few reads a node, where a walk of
// its paths, or a memo keyed by the binders or the depth around a part, or by
// the names the part binds, would make more.
test("the report's digest reads a shared object once", () => {
  const levels = 22, type = { tag: "Var", name: "A" };
  const at = (path, dim) => ({ tag: "PApp", path: { tag: "Var", name: path }, arg: [[`${dim}:1`]] });
  const system = term => [{ face: [["k:1"]], term }];
  // A binder whose body is read, by a getter when it is one.
  const binder = (tag, name, body, domain = type) => Object.freeze(Object.defineProperties(tag === "Lam" ? { tag, name, domain } : { tag, dim: name, family: type },
    { body: typeof body === "function" ? { get: body, enumerable: true } : { value: body, enumerable: true } }));
  // Free x and i, outside the binders of a lambda that holds them.
  const near = at("x", "i");
  // Each level applies one branch to another, each binding the level below.
  const shapes = {
    unused: { base: { tag: "Var", name: "x" }, branches: (level, read) =>
      [binder("Lam", `u${level}`, read), binder("Lam", `w${level}`, binder("PLam", `e${level}`, read))] },
    closed: {
      base: { tag: "App", fn: { tag: "App", fn: binder("Lam", "x", { tag: "Var", name: "x" }), arg: binder("PLam", "i", at("p", "i")) },
        arg: { tag: "App", fn: { tag: "Comp", dim: "i", family: type, system: system(at("p", "i")), base: { tag: "Var", name: "b" } },
          arg: { tag: "HComp", dim: "i", family: type, system: system(at("q", "i")), base: { tag: "Var", name: "b" } } } },
      branches: (level, read) => [binder("Lam", "x", binder("PLam", "i", read)), binder("Lam", "y", binder("PLam", "j", read))] },
    rebound: { base: at("x", "i"), branches: (level, read) =>
      [binder("Lam", "x", binder("PLam", "i", read), near), binder("Lam", "y", binder("PLam", "j", binder("Lam", "x", binder("PLam", "i", read), near)), near)] },
  };
  for (const [name, { base, branches }] of Object.entries(shapes)) {
    let reads = 0, value = base;
    for (let level = 0; level < levels; level++) {
      const part = value, [fn, arg] = branches(level, () => { reads++; return part; });
      value = Object.freeze({ tag: "App", fn, arg });
    }
    const { objects } = sharedNormalDigest(value), read = reads;
    assert.equal(objects, distinctObjects(value), name);
    assert.ok(read <= 4 * levels, `${name}: ${read} reads`);
  }
});

// Parts alike up to the names of bound variables and dimensions count once
// among the distinct parts, and one object met under bindings that give it
// two digests counts twice.
test("the report's digest counts distinct parts up to bound names", () => {
  const type = { tag: "Var", name: "A" }, path = { tag: "Var", name: "p" }, x = { tag: "Var", name: "x" };
  const identity = name => ({ tag: "Lam", name, domain: type, body: { tag: "Var", name } });
  const loop = dim => ({ tag: "PLam", dim, family: type, body: { tag: "PApp", path, arg: [[`${dim}:1`]] } });
  const counts = value => { const { objects, distinct } = sharedNormalDigest(value); return { objects, distinct }; };
  // App, both lambdas and their variables, and A; the lambdas alike, and their variables.
  assert.deepEqual(counts({ tag: "App", fn: identity("x"), arg: identity("y") }), { objects: 6, distinct: 4 });
  // App, both paths, A, both applications, p, and both formulas with their
  // clauses; the paths alike, their applications, formulas and clauses.
  assert.deepEqual(counts({ tag: "App", fn: loop("i"), arg: loop("j") }), { objects: 11, distinct: 7 });
  // A system and its tubes count as objects do. An empty system: the
  // composition, A, the system and b, each distinct.
  const b = { tag: "Var", name: "b" };
  assert.deepEqual(counts({ tag: "Comp", dim: "i", family: type, system: [], base: b }), { objects: 4, distinct: 4 });
  // Two compositions alike up to their binders, each with a tube on k whose
  // term names its binder: twenty objects, and App, the composition, A, the
  // system, the tube, its face formula and clause, its term's application,
  // p, formula and clause, and b distinct.
  const comp = dim => ({ tag: "Comp", dim, family: type, system: [{ face: [["k:1"]], term: { tag: "PApp", path, arg: [[`${dim}:1`]] } }], base: b });
  assert.deepEqual(counts({ tag: "App", fn: comp("i"), arg: comp("j") }), { objects: 20, distinct: 12 });
  // A composition's system counts as the same array a Glue term's does, and
  // its tubes as the same objects: empty, the system once among seven
  // objects; with one tube on k each, the system, the tube, its formula and
  // clause once each among fourteen.
  const t = { tag: "Var", name: "t" };
  const mixed = system => ({ tag: "App", fn: { tag: "Comp", dim: "i", family: type, system: system(), base: b },
    arg: { tag: "GlueTerm", as: type, base: b, system: system() } });
  assert.deepEqual(counts(mixed(() => [])), { objects: 7, distinct: 6 });
  assert.deepEqual(counts(mixed(() => [{ face: [["k:1"]], term: t }])), { objects: 14, distinct: 10 });
  // x bound under the lambda and free beside it.
  assert.deepEqual(counts({ tag: "App", fn: { tag: "Lam", name: "x", domain: type, body: x }, arg: x }), { objects: 4, distinct: 5 });
  // Applications alike up to their bound names, whose free names sort in
  // different orders: a before m, and q after it.
  const m = { tag: "Var", name: "m" }, apply = name => ({ tag: "Lam", name, domain: type, body: { tag: "App", fn: { tag: "Var", name }, arg: m } });
  assert.deepEqual(counts({ tag: "App", fn: apply("a"), arg: apply("q") }), { objects: 9, distinct: 6 });
});

// Two constructors of one module, and constructors of one name in two.
test("the report's digest tells constructors apart by name and module across programs", async t => {
  const values = [];
  for (const [owner, constructor] of [["main", "first_flag"], ["main", "second_flag"], ["left", "lit"], ["right", "lit"]]) {
    const { program, verdicts } = await checkProgram(t, `inductive Flag {\n  ${constructor};\n}\n\ndef flag := ${constructor};`, { module, name: owner });
    assert.equal(verdicts.flag, true, `${owner} ${constructor}`);
    values.push(digested(program, definitionValue(program, "flag", owner)));
  }
  for (const [left, right] of [[0, 1], [2, 3]]) {
    assert.notEqual(values[left].decoded, values[right].decoded);
    assert.notEqual(values[left].shared, values[right].shared);
  }
});
