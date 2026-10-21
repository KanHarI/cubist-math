import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import createCubical from "../web/dist/cubical.mjs";
import { tokenize, parse } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { lint } from "../web/cubist/lint.mjs";
import { checkProgram } from "./check-program.mjs";

// Evaluation demand marks (docs/roadmaps/runtime/evaluation-demand-marks.md):
// `!` asks for a part's weak head and `!!` for its full normal form, and an
// unmarked part of a pattern is computed only as far as the pattern observes
// it. The cases with messages are cubist-tests/evaluate_patterns.cubist;
// here, the tokens, the values evaluations report, what is left uncomputed,
// the normalize guard, and every construct of the language.
const module = await createCubical();

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
  ]);
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
});

test("demand marks format tightly and lint what asks for nothing more", () => {
  const source = "evaluate  !! e expecting ( ! _ , cons( !!_ , ! (1, _) ) ) ;\n";
  const formatted = formatCubist(source);
  assert.equal(formatted, "evaluate !!e expecting (!_, cons(!!_, !(1, _)));\n");
  assert.equal(formatCubist(formatted), formatted);
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
    const { result } = await checkProgram(t, lines.join("\n"), { module });
    const outcome = new Map([...result.evaluations.map(evaluation => [evaluation.start, evaluation.value]),
      ...result.gaps.filter(gap => gap.directive).map(gap => [gap.declarationStart, { refused: gap.code }])]);
    const source = lines.join("\n"), lineOf = offset => source.slice(0, offset).split("\n").length;
    const outcomes = new Map([...outcome].map(([start, value]) => [lineOf(start), value]));
    for (const [line, [item, mark]] of at) {
      const value = outcomes.get(line);
      if (item.refused) { assert.deepEqual(value, { refused: item.refused }, `${item.id} ${mark}`); continue; }
      assert.equal(typeof value, "string", `${item.id} ${mark}: ${JSON.stringify(value)}`);
      if (mark === "!_") assert.ok(shownHead(item.whnf)(value), `${item.id}: ${value} is not ${item.whnf}`);
      else assert.doesNotMatch(value, /<unevaluated>|<fun>|<type>/, `${item.id}: a full normal form`);
    }
  });
}
