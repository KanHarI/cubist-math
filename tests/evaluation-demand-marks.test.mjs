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
import { normalDigest } from "../tools/evaluation-baseline.mjs";
import { reported } from "../tools/inline-errors.mjs";
import { printedNodes, valueForm } from "../web/translator/evaluation.mjs";
import { sharedDigest } from "../docs/roadmaps/runtime/evaluation-demand-marks/shared-digest.mjs";

// Evaluation demand marks (docs/roadmaps/runtime/evaluation-demand-marks.md):
// `!` asks for a part's weak head and `!!` for its full normal form, and an
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
  const { evaluated, displayText } = checker, { head, normalize } = kernel;
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
  kernel.normalize = function (handle) {
    // Directives run in turn, and a later one may check the same term to the
    // same handle: the normalization is the latest evaluation's.
    asked.push({ query: "normalize", handle });
    const result = normalize.call(this, handle);
    if (evaluations.at(-1)?.handle === handle) Object.assign(evaluations.at(-1), { normalized: true, normal: checker.decoded(result) });
    return result;
  };
  return { program, evaluations, asked };
}

test("! and !! are tokens, read only right after evaluate and in an expected pattern", () => {
  assert.deepEqual(tokenize("!!_ !_ ! !").slice(0, -1).map(token => token.text), ["!!", "_", "!", "_", "!", "!"]);
  const [directive] = parse("evaluate !!e expecting (!_, cons(1, !!_));").directives;
  assert.equal(directive.mark, "!!");
  assert.equal(directive.expected.left.kind, "demand");
  assert.equal(directive.expected.left.mark, "!");
  assert.equal(directive.expected.right.args[1].mark, "!!");
  // Two marks apart would read as !! but ask for a weak head.
  assert.throws(() => parse("evaluate e expecting ! !_;"), /Two ! marks apart/);
  assert.throws(() => parse("evaluate ! !e expecting _;"), /Two ! marks apart/);
  // print(evaluate(…)) takes a mark before its term, and nowhere else.
  assert.equal(parse("print(evaluate(!!e));").directives[0].mark, "!!");
  for (const source of ["def x := !3;", "evaluate !(!e) expecting _;", "print(typeof(!e));", "print(evaluate(f(!e)));"])
    assert.throws(() => parse(source), /The demand mark ! stands right after evaluate/, source);
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

test("print(evaluate(e)) shows the value form, !e the weak head as it is, and !!e the full normal form", async t => {
  const { result } = await checkProgram(t, `import unat;
use unat;
def double(n : UNat) := n + n;
def pair_ : UNat and (UNat -> UNat) := (double(3), double);
def far : UNat and UNat := (2 * 255, 2 * 255);
print(evaluate(pair_));
print(evaluate(!pair_));
print(evaluate(!!pair_));
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
print(evaluate(far));`, { module });
  // euclid(4)'s prime has a weak head too deep to build (K344), and neither
  // print reaches it.
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

test("the value form computes no more heads than the printer shows", async t => {
  const queries = async source => {
    const { program, result } = await checkProgram(t, `import lists;
use unat;
def hundreds(n : UNat) : List(U0, UNat) := match n {
  zero => nil;
  succ(k) => cons(100, hundreds(k));
};
${source}`, { module });
    assert.deepEqual(result.gaps.map(gap => gap.reason), [], source);
    return { queries: Number(program.kernel.work().queries), text: result.prints[0]?.text };
  };
  const none = await queries(""), some = await queries("print(evaluate(hundreds(250)));");
  // 250 elements of 102 heads each are past the budget of 4,000 heads.
  assert.ok(some.queries - none.queries <= 4100, `the walk asked ${some.queries - none.queries} queries`);
  assert.match(some.text, /^cons\(100, cons\(100, /);
});

test("the value form shows no part deeper than the kernel's terms, however deep the value", async t => {
  const run = async source => {
    const { program, result } = await checkProgram(t, `import unat;
use unat;
def d := 2 * 256;
def deep := d + d + d + d + d + d + d + d;
${source}`, { module });
    assert.deepEqual(result.gaps.map(gap => gap.reason), [], source);
    return { queries: Number(program.kernel.work().queries), text: result.prints[0]?.text };
  };
  // 4096 levels of succ: the walk keeps its own stack, and computes heads
  // only to 512 levels, where the kernel's own terms end.
  const none = await run(""), deep = await run("print(evaluate(deep));");
  assert.match(deep.text, /^succ\(succ\(succ\(/);
  assert.ok(deep.queries - none.queries <= 600, `the walk asked ${deep.queries - none.queries} queries`);
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
    assert.equal(await shown("evaluate !!f;"), "fun (n : UNat) => induction n return UNat { zero => 1; succ h => succ(h); }");
    assert.equal(await shown("!!f;"), await shown("evaluate !!f;"));
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
  const prime = await ticks("evaluate value expecting (7, _);"), full = await ticks("evaluate value expecting !!_;");
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
  assert.equal(checker.displayText(checker.normalForm(first)), "unat.(3)");
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
  assert.equal(checker.displayText(checker.normalForm(inner)), "unat.(2)");
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
  assert.equal(checker.displayText(checker.normalForm(inner.children[1])), "unat.(1)");
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
  // A mark before another stays apart from it: ! !!_ is not !!!_.
  for (const [written, shown] of [["evaluate tt expecting ! !!_;", "evaluate tt expecting ! !!_;\n"],
    ["evaluate tt expecting (!  !!_, !! !_);", "evaluate tt expecting (! !!_, !! !_);\n"]]) {
    assert.equal(formatCubist(written), shown);
    assert.equal(formatCubist(shown), shown);
  }
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
});

// One closed example of every construct with a term to evaluate, and its
// weak head on main, from the demand marks note. Each evaluates under !_,
// shown as its recorded head, under !!_, and printed, as its value form,
// except the assumptions, which evaluation refuses. Three examples whose full normal forms cost about 30
// seconds each are evaluated under !_ only; the DM5 report
// (docs/roadmaps/runtime/evaluation-demand-marks/report.md) records that
// they complete.
const corpus = JSON.parse(readFileSync(new URL("../docs/roadmaps/runtime/evaluation-demand-marks/constructs.json", import.meta.url), "utf8"));
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
  test(`every construct of setup ${setup} evaluates under !_ and !!_ and prints`, async t => {
    // Each directive's line names its construct.
    const lines = [corpus.setups[setup], ""], at = new Map();
    items.forEach((item, index) => {
      lines.push(`def probe_${index} := ${item.term};`);
      for (const mark of slowNormalForms.has(item.id) ? ["!_"] : ["!_", "!!_"]) {
        at.set(lines.join("\n").split("\n").length + 1, [item, mark]);
        lines.push(`evaluate probe_${index} expecting ${mark};`);
      }
      at.set(lines.join("\n").split("\n").length + 1, [item, "print"]);
      lines.push(`print(evaluate(probe_${index}));`);
    });
    const { program, evaluations } = recordedProgram(t), result = await program.check(lines.join("\n"), "main");
    const outcome = new Map([...result.evaluations.map(evaluation => [evaluation.start, evaluation.value]),
      ...result.prints.map(print => [print.start, print.text]),
      ...result.gaps.filter(gap => gap.directive).map(gap => [gap.declarationStart, { refused: gap.code }])]);
    const source = lines.join("\n"), lineOf = offset => source.slice(0, offset).split("\n").length;
    const outcomes = new Map([...outcome].map(([start, value]) => [lineOf(start), value]));
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
      assert.equal(typeof value, "string", `${item.id} ${mark}: ${JSON.stringify(value)}`);
      assert.equal(wholeNormalized, mark === "!!_", `${item.id} ${mark}: the whole term ${mark === "!!_" ? "is" : "is not"} normalized`);
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
      } else if (mark === "!!_") {
        // What !!_ shows is the normal form the kernel computed, up to the
        // names of bound variables.
        assert.doesNotMatch(value, /<unevaluated>|<fun>|<type>/, `${item.id}: a full normal form`);
        assert.equal(normalDigest(evaluation.shown), normalDigest(evaluation.normal), `${item.id}: the kernel's normal form is shown`);
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
        // Where it marks nothing, it is the full normal form.
        const normal = outcomes.get([...at].find(([, [other, kind]]) => other === item && kind === "!!_")?.[0]);
        if (!/[<…]/.test(value) && typeof normal === "string" && !normal.includes("…"))
          assert.equal(value, normal, `${item.id}: the value form of data is its normal form`);
      }
    }
  });
}

// The acceptance report (docs/roadmaps/runtime/evaluation-demand-marks/
// report.md) compares normal forms by a digest over the kernel's shared
// nodes, as normal forms too large to decode need. It must tell terms apart
// exactly as the baseline's digest of their decodings does: up to the names
// of bound variables and dimensions and the slots the kernel gives them, and
// no further, across programs as well as within one.
const digested = (program, value) => ({ shared: sharedDigest(program, value).normalDigest,
  decoded: normalDigest(program.checker.syntax.decode(value, program.checker.dimensions)) });
const definitionValue = (program, name) => program.kernel.definition(program.kernel.definitions.get(`main__${name}`)).value;
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

test("the report's digest tells constructors apart by name across programs", async t => {
  const values = [];
  for (const constructor of ["first_flag", "second_flag"]) {
    const { program, verdicts } = await checkProgram(t, `inductive Flag {\n  ${constructor};\n}\n\ndef flag := ${constructor};`, { module });
    assert.equal(verdicts.flag, true, constructor);
    values.push(digested(program, definitionValue(program, "flag")));
  }
  assert.notEqual(values[0].decoded, values[1].decoded);
  assert.notEqual(values[0].shared, values[1].shared);
});
