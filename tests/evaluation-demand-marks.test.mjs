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
  for (const source of ["def x := !3;", "evaluate !(!e) expecting _;", "print(evaluate(!e));"])
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

test("an exact expected value computes the normal form before the assumptions are checked, and a pattern after", async t => {
  const { result } = await checkProgram(t, `import unat;
use unat;
def mixed := TruncateIntro(U0, UNat, 2 * 256);
evaluate mixed expecting mixed;
evaluate mixed expecting !_;`, { module });
  assert.deepEqual(result.gaps.filter(gap => gap.directive).map(gap => gap.code), ["K344", "E324"]);
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
// shown as its recorded head, and under !!_, except the assumptions, which
// evaluation refuses. Three examples whose full normal forms cost about 30
// seconds each are evaluated under !_ only; the note records that they
// complete.
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
for (const setup of Object.keys(corpus.setups)) {
  const items = corpus.constructs.filter(item => item.setup === setup);
  if (!items.length) continue;
  test(`every construct of setup ${setup} evaluates under !_ and !!_`, async t => {
    // Each directive's line names its construct.
    const lines = [corpus.setups[setup], ""], at = new Map();
    items.forEach((item, index) => {
      lines.push(`def probe_${index} := ${item.term};`);
      for (const mark of slowNormalForms.has(item.id) ? ["!_"] : ["!_", "!!_"]) {
        at.set(lines.join("\n").split("\n").length + 1, [item, mark]);
        lines.push(`evaluate probe_${index} expecting ${mark};`);
      }
    });
    const { program, evaluations } = recordedProgram(t), result = await program.check(lines.join("\n"), "main");
    const outcome = new Map([...result.evaluations.map(evaluation => [evaluation.start, evaluation.value]),
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
      } else {
        // What !!_ shows is the normal form the kernel computed, up to the
        // names of bound variables.
        assert.doesNotMatch(value, /<unevaluated>|<fun>|<type>/, `${item.id}: a full normal form`);
        assert.equal(normalDigest(evaluation.shown), normalDigest(evaluation.normal), `${item.id}: the kernel's normal form is shown`);
      }
    }
  });
}
