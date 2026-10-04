// match on declared types, work-plan L2.2a: clauses elaborated against the
// clause types the kernel computes, dependent motives, path and squash
// clauses, structural recursion, the refusals, and the H1 release fixture:
// the circle's winding number, computed through univalence. The cases are
// cubist-tests/declared_match.cubist, whose comments state each error and
// warning (tests/cubist-tests.test.mjs compares them with its check); the
// tests here check what a verdict does not show: evaluations, the fuel spent
// and the goals shown, and what is not one module's: syntax, a kernel
// session's options and the winding fixture.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { checkProgram, testModule } from "./check-program.mjs";

const module = await createCubical();
const check = (t, source) => checkProgram(t, source, { module });
const cases = testModule("declared_match", { module });
const ok = declaration => assert.ok(declaration.verified, `${declaration.name}: ${declaration.reason}`);
const refused = (declaration, pattern) => {
  assert.equal(declaration.verified, false, `${declaration.name} was accepted`);
  assert.match(declaration.reason, pattern);
};

// E1: the winding number, by S1's eliminator into U0 with ua of the
// successor equivalence. E2 in substance: code_on_loop, cong(code, loop)
// equal to ua(succ) by rfl.
test("the H1 release fixture: the circle's winding number computes through univalence", async t => {
  const source = await readFile(new URL("../docs/examples/h1/winding.cubist", import.meta.url), "utf8");
  const { result, get } = await check(t, source);
  for (const name of ["succ_equiv", "code", "winding", "winding_loop", "winding_twice", "winding_back", "code_on_loop"]) {
    ok(get(name));
    assert.deepEqual(get(name).extensions, []);
    assert.deepEqual(get(name).axioms, [], `${name} uses no assumption: it computes`);
  }
  assert.deepEqual(result.evaluations.map(evaluation => evaluation.value),
    ["pos(succ(zero))", "pos(succ(succ(succ(zero))))", "pos(zero)"]);
  assert.ok(result.complete);
});

test("the formatter keeps a qualified name's dot tight", async () => {
  const { formatCubist } = await import("../web/cubist/formatter.mjs");
  const source = "def same(x, y : Trunc(U0, Nat)) : x = y := Trunc.squash(x, y);\n";
  const formatted = formatCubist(source);
  assert.match(formatted, /Trunc\.squash\(x, y\)/);
  assert.equal(formatCubist(formatted), formatted);
});

test("nested legacy matches are walked once: parsing and formatting stay linear", async () => {
  const { parse } = await import("../web/cubist/parser.mjs");
  const { formatCubist } = await import("../web/cubist/formatter.mjs");
  let body = "0";
  for (let depth = 0; depth < 40; depth++) body = `match x return Nat { left a => ${body}; right b => 0; }`;
  const source = `def deep(x : Nat or Nat) : Nat := ${body};\n`;
  const started = performance.now();
  const match = parse(source).declarations[0].body[0].value;
  assert.ok(match.leftBody && match.clauses.length === 2, "the legacy fields and the clauses are both there");
  assert.ok(!Object.keys(match).includes("clauses"), "the legacy shape's clauses are not enumerated");
  formatCubist(source);
  assert.ok(performance.now() - started < 5000, "a doubled walk would take 2^40 steps");
});

test("the formatter keeps a qualified squash clause's dot tight", async () => {
  const { formatCubist } = await import("../web/cubist/formatter.mjs");
  const source = "def f(t : T) : T := match t { T.squash(x, y) @ i => x; };\n";
  assert.match(formatCubist(source), /T\.squash\(x, y\) @ i => x;/);
});

// L2.2a's third slice: a recursive call passes values of its own for the
// declaration's other parameters. The motive quantifies over each of them but
// those the matched parameter's type depends on, and each clause binds them
// again under their own names.
test("recursion whose other arguments vary: the accumulator, computed and proved", async () => {
  const { result, get } = await cases();
  for (const name of ["acc", "acc_first", "two_three", "add_succ", "acc_add"]) ok(get(name));
  assert.deepEqual(result.evaluations.map(evaluation => evaluation.value), ["succ(succ(zero))", "succ(succ(succ(zero)))"]);
});

// An abandoned first attempt spends nothing of the declaration's. The two
// proofs are the same but for their type's constructor order: once's first
// attempt checks its simp before reaching the call that changes a, and
// abandons it; again's reaches that call first. Both record what their kept
// attempt spent, and only that.
test("recursion whose other arguments vary: an abandoned attempt spends nothing", async () => {
  const { get } = await cases();
  for (const name of ["once", "again", "plain"]) ok(get(name));
  const spent = name => [get(name).searchFuel.queries, get(name).searchFuel.searches];
  assert.deepEqual(spent("once"), spent("again"));
  // What the kept attempt spent is the declaration's: more than its simp alone.
  assert.ok(spent("once")[0] > spent("plain")[0] && spent("once")[1] === spent("plain")[1]);
});

// An operator that stands for the declaration calls it as its name does:
// cubist-tests/declared_match_operator_call.cubist.

// A clause's goal shows a generalized parameter under its own name, without
// the parameter it supersedes; its recursive result quantifies over it. A
// recursion that passes its parameters unchanged keeps them fixed, and the
// first attempt of one that changes them leaves no second set of steps.
test("a clause's goal shows a generalized parameter under its source name", async () => {
  const { program } = await cases();
  const shown = name => program.steps("declared_match").filter(step => step.declaration === name)
    .map(step => [step.kind, step.locals.map(local => `${local.name} : ${local.type}`), step.goal]);
  assert.deepEqual(shown("acc_add"), [
    ["matchStatement", ["n : N", "a : N"], "acc(n, a) = add(n, a)"],
    ["rfl", ["n : N", "a : N"], "acc(zero, a) = add(zero, a)"],
    ["exact", ["n : N", "m : N", "m_rec : forall a : N. acc(m, a) = add(m, a)", "a : N"], "acc(succ(m), a) = add(succ(m), a)"],
  ]);
  assert.deepEqual(shown("add_succ").at(-1), ["exact", ["n : N", "a : N", "m : N", "m_rec : add(m, succ(a)) = succ(add(m, a))"],
    "add(succ(m), succ(a)) = succ(add(succ(m), a))"]);
  // Nor a second set of inspector records: the clause binds m once.
  assert.equal(program.declarationBindings.get("declared_match__acc_add").filter(item => item.node.name === "m").length, 1);
  // A parameter whose name ends in a digit is shown once too.
  const clause = program.steps("declared_match").find(step => step.declaration === "same_a1" && step.kind === "exact");
  assert.deepEqual(clause.locals.filter(local => local.name.startsWith("a1")).map(local => local.type), ["N"]);
});

test("with declared types switched off in the kernel, the match statement says so", async t => {
  const program = new CubicalProgram(module, sourceReader(), {prelude:false});
  t.after(() => program.dispose());
  program.kernel.setExtensions({ h1: false });
  const result = await program.check("def f(n : Unit) : Unit {\n  match n {\n    zero => { exact n; }\n  }\n}\n", "main");
  refused(result.outputs.find(output => output.name === "f"),
    /^The match statement takes apart a value of a declared type, and declared types \(H1\) are switched off in this kernel session\./);
});

test("the match statement parses and formats, one statement to a line", async () => {
  const { parse } = await import("../web/cubist/parser.mjs");
  const { formatCubist } = await import("../web/cubist/formatter.mjs");
  const source = "def add_zero(n : N) : add(n, zero) = n {\n  match n {\n    zero => {\n      rfl;\n    }\n    succ(m) => {\n      exact cong(succ, add_zero(m));\n    }\n  }\n}\n";
  const statement = parse(source).declarations[0].body[0];
  assert.equal(statement.kind, "matchStatement");
  assert.deepEqual(statement.clauses.map(clause => clause.constructor.text), ["zero", "succ"]);
  assert.equal(formatCubist(source), source);
  assert.throws(() => parse("def f(n : N) : N {\n  match n as k return N { zero => { exact n; } }\n}\n"),
    /The match statement takes its motive from the goal/);
  assert.throws(() => parse("def f(n : N) : N {\n  match n { zero => n; }\n}\n"),
    /A clause of the match statement is a proof block/);
  // Several values, each clause a pattern for each (cubist-tests/patterns).
  assert.equal(parse("def f(n, m : N) : N {\n  match n, m { zero, k => { exact m; } }\n}\n").declarations[0].body[0].values.length, 2);
});

