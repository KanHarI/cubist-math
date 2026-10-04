// match on declared types, work-plan L2.2a: clauses elaborated against the
// clause types the kernel computes, dependent motives, path and squash
// clauses, structural recursion, the refusals, and the H1 release fixture:
// the circle's winding number, computed through univalence. The cases are
// cubist-tests/declared_match.cubist, checked once; the tests here look its
// declarations up by name.
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

test("structural recursion computes, with a parameter held fixed", async () => {
  const { get } = await cases();
  for (const name of ["add", "double", "four", "three"]) ok(get(name));
  refused(get("wrong"), /./);
});

test("a dependent motive: each clause is checked at its own instance", async () => {
  const { get } = await cases();
  ok(get("zero_right"));
});

test("data before positions: clauses name arguments in the order declared", async () => {
  const { get } = await cases();
  for (const name of ["size", "labels", "two", "one"]) ok(get(name));
});

test("a path constructor's clause is a path between the clauses at its ends", async () => {
  const { get } = await cases();
  ok(get("flat"));
  ok(get("at_loop"));
  refused(get("torn"), /mismatch|clause/i);
  refused(get("unnamed"), /loop is a path constructor: name its 1 dimension after its arguments, as in loop @ i => …/);
  refused(get("extra"), /base has no dimensions to name/);
  // A coordinate follows @, as in the point the clause covers.
  refused(get("bare"), /Write the dimension of loop after @, as the point the clause covers: loop @ i => …/);
});

// E3: a truncation's eliminator, with its squash clause written T.squash.
// E8: without an explicit squash clause or checked h-level evidence, refused.
test("a truncation's squash clause, with T.squash and recursive results", async () => {
  const { get } = await cases();
  for (const name of ["same", "rebuilt", "rebuilt_point"]) ok(get(name));
  refused(get("unsquashed"), /Cannot generate Trunc\.squash: import hlevels.*h-level evidence/);
});

// E8: a missing clause, a duplicate clause and an unknown constructor.
test("the refusals name the clause or the call", async () => {
  const { get } = await cases();
  refused(get("unknown"), /N has no constructor tail: its constructors are zero, succ/);
  refused(get("twice"), /zero has two clauses/);
  refused(get("partial"), /match on N needs a clause for succ/);
  refused(get("arity"), /succ takes 1 argument here/);
  refused(get("growing"), /not on an argument of the matched constructor: only structural recursion/);
  refused(get("outside"), /outside is being defined: it can call itself only on an argument of a constructor/);
  refused(get("untyped"), /match needs its result's type/);
  refused(get("on_nat"), /match requires a value of a declared type, or of a sum/);
});

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


test("recursion recognizes the declaration's own parameter by its binder, not by its name", async () => {
  const { get } = await cases();
  // The inner n is another variable: a call there is not recursion on it.
  refused(get("tricky"), /tricky is being defined: it can call itself only on an argument of a constructor/);
  // A clause may name its argument as the parameter was named.
  ok(get("shadowed"));
});

test("recursion only where the match is the whole body, and with the matched parameter rebound", async () => {
  const { get } = await cases();
  // Around the match, a call's recursive result would omit the succ.
  refused(get("wrapped"), /wrapped is being defined: it can call itself only on an argument of a constructor/);
  // n in the zero clause is zero there, on every recursive call: f is constant zero.
  for (const name of ["captured", "constant_zero", "via_block", "via_value"]) ok(get(name));
  refused(get("not_identity"), /./);
});

test("a clause's own names shadow the declaration's name and its matched parameter", async () => {
  const { get } = await cases();
  for (const name of ["f", "predecessor", "g", "also_predecessor"]) ok(get(name));
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

test("recursive calls are the calls written: their types, arities and arguments", async () => {
  const { get } = await cases();
  // tagged(m) has type Tag(m), not Tag(n): the succ clause needs Tag(succ(m)).
  refused(get("tagged"), /mismatch/i);
  refused(get("outer_motive"), /The motive mentions n itself: write it over the matched value/);
  ok(get("refl_all"));
  refused(get("applied"), /m takes 0 arguments here, as an argument of the matched constructor/);
  // p is generalized: in the succ clause it proves succ(m) = zero, and the
  // call needs m = zero.
  refused(get("dep"), /Type mismatch: found succ\(m\) = zero, expected m = zero/);
  // A parameter named as the declaration is.
  ok(get("h"));
  ok(get("shadowed_by_parameter"));
});

test("third review: a path of the matched type is recursed on at its dimensions", async () => {
  const { get } = await cases();
  // p : x = y is not an S: ill_typed(p) would be ill-typed outside the definition.
  refused(get("ill_typed"), /p is a 1-dimensional path of the matched type, not an element: call ill_typed on it at its dimensions, as ill_typed\(p @ i\)/);
  ok(get("rebuilt_set"));
  ok(get("rebuilt_set_point"));
  refused(get("too_many"), /x is an element of the matched type, not a path/);
});

test("third review: a parameter that shadows its type's name still matches", async () => {
  const { get } = await cases();
  ok(get("count"));
  ok(get("counted"));
});

test("fourth review: a user constructor named squash and the generated T.squash are distinct clauses", async () => {
  const { get } = await cases();
  for (const name of ["keep", "kept", "qualified"]) ok(get(name));
  // squash here is the user's constructor: two clauses for it.
  refused(get("ambiguous"), /squash has two clauses/);
  const { formatCubist } = await import("../web/cubist/formatter.mjs");
  const source = "def f(t : T) : T := match t { T.squash(x, y) @ i => x; };\n";
  assert.match(formatCubist(source), /T\.squash\(x, y\) @ i => x;/);
});

test("fifth review: a position's arguments may be curried in a recursive call", async () => {
  const { get } = await cases();
  for (const name of ["curried_size", "curried_size_flat", "curried_one"]) ok(get(name));
  refused(get("curried_partial"), /p takes 2 arguments here, as an argument of the matched constructor/);
});

// The closing proof statement (L2.2a through the HoTT roadmap's A5): its
// motive is the goal over the matched value, and each clause is a proof
// block of the goal at its constructor.
test("the match statement proves the goal at each constructor, recursing by name", async () => {
  const { get } = await cases();
  for (const name of ["add_zero", "IsZero", "zero_of", "zero_named", "zero_named_after_intro", "local_fact", "local_value", "nested_copy",
    "simp_at_generalized", "constructor_scrutinee", "same_value", "same_value_two", "after_intro"]) ok(get(name));
});

test("a match statement's generalized hypothesis takes its own value at a recursive call", async () => {
  const { get } = await cases();
  for (const name of ["Rep", "total_by_statement", "seven_by_statement"]) ok(get(name));
  refused(get("unchanged"), /mismatch/i);
});

// A match inside a recursive clause: the recursive call still names the
// variable the inner match takes apart, at its constructor there.
test("a nested match statement keeps the enclosing recursion", async () => {
  const { get } = await cases();
  // A position the inner match generalizes, as p : Tag(k) -> W is, is
  // recursed on under its new variable.
  for (const name of ["nested", "deep", "keep_acc", "keep_acc_two", "Tag", "W", "count_w"]) ok(get(name));
  refused(get("not_smaller"), /not on an argument of the matched constructor/);
});

test("a match statement recurses on several arguments of a constructor, with a parameter fixed", async () => {
  const { get } = await cases();
  for (const name of ["mirror", "mirror_mirror"]) ok(get(name));
});

// A truncation's squash clause, written in the statement: a path between the
// recursive results at its ends.
test("a match statement's squash clause", async () => {
  const { get } = await cases();
  // A universe parameter passes unchanged as a type parameter does.
  for (const name of ["rebuilt_by_statement", "rebuilt_by_statement_point", "generic", "generic_point"]) ok(get(name));
});

test("a match statement's path clause is a path between the clauses at its ends", async () => {
  const { get } = await cases();
  for (const name of ["flat", "flat_constant"]) ok(get(name));
});

test("the match statement's refusals", async () => {
  const { get } = await cases();
  refused(get("unreachable"), /^Statements after match are unreachable: each clause's block closes the goal\./);
  refused(get("missing"), /match on N needs a clause for succ\./);
  refused(get("of_a_sum"), /^The match statement takes apart a value of a declared type; for a sum, use cases\./);
  refused(get("wrong_clause"), /./);
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

// A parameter whose type mentions a generalized one is generalized too; a
// clause's own name shadows a parameter's; a nested match takes apart a
// generalized parameter, and a call passes its constructor.
test("recursion whose other arguments vary: dependent, shadowed and nested parameters", async () => {
  const { get } = await cases();
  for (const name of ["Rep", "dep_ok", "bounded", "sh", "sh_value", "inner", "inner_value"]) ok(get(name));
  // A dependent parameter used at its refined type before the call: the
  // match as written fails there, and the one over the other parameters
  // stands, since it makes the call.
  for (const name of ["total", "seven"]) ok(get(name));
  // Without a call the expression is the match as written, whose motive does
  // not refine r (the statement's does).
  refused(get("first"), /^Projection \.1 requires a dependent pair; found a value of type Rep\(n\)\./);
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

test("recursion whose other arguments vary: what stays fixed, and path and squash clauses", async () => {
  const { get } = await cases();
  // A match that never calls its declaration keeps its motive, whatever its
  // binders are named: the declaration is the match as written.
  for (const name of ["pick", "pick_unfolds", "own", "own_unfolds"]) ok(get(name));
  refused(get("relabel"), /^A recursive call of relabel passes A unchanged: the type of the matched t depends on it\./);
  refused(get("lift"), /^A recursive call of lift passes the universe parameter U unchanged\./);
  // A clause over a generalized parameter is a path of functions, and the
  // kernel still checks it against the clauses at its ends.
  for (const name of ["around", "around_loop", "Steps", "count_steps", "count_steps_two"]) ok(get(name));
  refused(get("torn_varying"), /mismatch|clause/i);
  refused(get("skewed"), /mismatch|clause/i);
});

// An operator that stands for the declaration calls it as its name does.
test("recursion whose other arguments vary: a call spelled with an operator", async t => {
  const { get } = await check(t, `inductive N { zero; succ(n : N); }
def add(n, a : N) : N := match n { zero => a; succ(m) => m + succ(a); };
def five : add(succ(succ(zero)), succ(succ(succ(zero)))) = succ(succ(succ(succ(succ(zero))))) { rfl; }
`);
  for (const name of ["add", "five"]) ok(get(name));
});

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

// The refactor shared with the statement keeps the expression's order: the
// declared type, then the motive, then the clauses.
test("the expression reports a missing motive before a missing clause", async () => {
  const { get } = await cases();
  refused(get("unknown_motive"), /^match needs its result's type: give return T, or use it where its type is known\./);
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
  assert.throws(() => parse("def f(n, m : N) : N {\n  match n, m { zero => { exact m; } }\n}\n"),
    /The match statement takes apart one value/);
});

