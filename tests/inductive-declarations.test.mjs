// `inductive` declarations, work-plan L2.1 (docs/roadmaps/h1-signature-
// specification.md, section 9): the header's result position, lowering to
// the normal form with data before positions, universe classification, the
// least level, uses of the type and its constructors, the kernel's H1 switch
// and the absence of the marker since H1's release (6.4), and the rejections.
// The cases are the cubist-tests/inductive_*.cubist modules, whose comments
// state each refusal and name each case (tests/cubist-tests.test.mjs); here,
// what a verdict does not show: the admitted signatures, types, markers,
// positions and inspection views.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { parse } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { checkTestModule } from "./check-program.mjs";

const module = await createCubical();
const library = name => readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8");
const naturals = "inductive N { zero; succ(n : N); }\n";
const refused = (declaration, pattern) => {
  assert.equal(declaration.verified, false, `${declaration.name} was accepted`);
  assert.match(declaration.reason, pattern);
};
// A test's module, checked for that test alone.
const cases = (t, name) => checkTestModule(t, `inductive_${name}`, { module });
// An admitted signature, by the module's binding.
const signature = (program, module, name) => program.kernel.signature(program.kernel.signatures.get(`inductive_${module}__${name}`).index);
// The line:column where errors report the first `text` after `anchor` in `source`.
const at = (source, text, anchor = "") => {
  const before = source.slice(0, source.indexOf(text, source.indexOf(anchor)));
  return `${before.split("\n").length}:${before.length - before.lastIndexOf("\n")}`;
};

// V31: the contextual words are h-levels only in a header's result
// position: Gpd's trunc(1), and prop as a definition's name; trunc(-2) is
// refused, stating the allowed levels.
test("the parser reads each header form, and the formatter keeps them", () => {
  const source = `inductive N { zero; succ(n : N); }
inductive Trunc(U < UU0, A : U) : prop U { point(a : A); }
inductive Flag : U1 { on; off; }
inductive Gpd(U < UU0, A : U) : trunc(1) { point(a : A); }
inductive Circle { base; loop : base = base; }
def prop(set : N) := set;
`;
  const { declarations } = parse(source);
  assert.deepEqual(declarations.map(d => d.kind), ["inductive", "inductive", "inductive", "inductive", "inductive", "def"]);
  assert.deepEqual(declarations.map(d => d.result?.modifier?.kind ?? null), [null, "prop", null, "trunc", null, null]);
  assert.equal(declarations[3].result.modifier.level, 1);
  assert.equal(declarations[2].result.universe.name, "U1");
  assert.equal(declarations[4].constructors[1].type.kind, "binary");
  const formatted = formatCubist(source);
  assert.match(formatted, /^inductive N \{\n {2}zero;\n {2}succ\(n : N\);\n\}\n\ninductive Trunc/);
  assert.equal(formatCubist(formatted), formatted);
  for (const [bad, message] of [["inductive X : { a; }", /h-level, a universe or both/],
    ["inductive X : trunc(x) { a; }", /integer level/], ["inductive X { a(U < UU0); }", /bind universes in the declaration's header/],
    ["inductive X { a", /Expected ';'/],
    ["inductive B : trunc(-2) { b; }", /trunc\(n\) needs n ≥ -1: prop is trunc\(-1\), set is trunc\(0\)\./]])
    assert.throws(() => parse(bad), message);
});


// T1: switched off in the kernel, a declaration is refused, saying so. The
// experimental option that once switched H1 on is gone.
test("declared types need no option, and are refused when switched off in the kernel", async t => {
  const program = new CubicalProgram(module, library);
  t.after(() => program.dispose());
  program.kernel.setExtensions({ h1: false });
  const result = await program.check(naturals, "main");
  refused(result.outputs.find(output => output.name === "N"), /Declared types \(H1\) are switched off in this kernel session/);
  assert.throws(() => new CubicalProgram(module, library, { experimental: ["h1"] }), /H1 is no longer experimental/);
});


// T2, directly and through a definition: since H1's release, no result that
// uses a declared type carries the marker (the specification's 6.4).
test("T2: no result that uses a declared type carries a marker, and types print by name", async t => {
  const { get } = await cases(t, "values");
  for (const name of ["N", "List", "two", "two_is_two", "one_two", "counted"]) {
    assert.deepEqual(get(name).extensions, [], `${name} carries no marker`);
    assert.deepEqual(get(name).axioms, []);
  }
  assert.deepEqual(get("plain").extensions, []);
  assert.equal(get("one_two").type, "List(N)");
  assert.equal(get("two").type, "N");
});

test("universe parameters: an erased one is read from its parameter, a recorded one carried", async t => {
  const { program } = await cases(t, "universes");
  const recorded = name => signature(program, "universes", name).recorded;
  assert.equal(recorded("List"), 0, "List's universe only bounds A's type");
  assert.equal(recorded("Pointed"), 1, "Pointed stores a type of its own universe");
  assert.equal(recorded("Lifted"), 1, "no parameter can read Lifted's universe");
});

// A11: data are moved ahead of positions, as the kernel requires.
test("A11: data are moved ahead of positions", async t => {
  const { program } = await cases(t, "data_first");
  const node = signature(program, "data_first", "Tree").constructors[1];
  assert.deepEqual([node.data, node.positions], [1, 2]);
});

test("a failed declaration admits nothing", async t => {
  const { program } = await cases(t, "failed");
  assert.equal(program.kernel.signatures.has("inductive_failed__Broken"), false);
});

// T2, through an import.
test("T2: an imported declared type is used by name, with no marker", async t => {
  const { get } = await cases(t, "imports");
  assert.deepEqual(get("three").extensions, []);
});

// T3: computable accepts a declared type. T4: an assumption is refused, and
// named alone.
test("T3, T4: computable accepts a declared type, and names only the assumption it refuses", async t => {
  const { get } = await cases(t, "computable");
  assert.deepEqual(get("marked").extensions, []);
  assert.doesNotMatch(get("both").reason, /H1|kernel extension/);
});

test("binders written in a constructor's result are its arguments", async t => {
  const { program } = await cases(t, "binders");
  assert.deepEqual(signature(program, "binders", "M").constructors.map(c => [c.data, c.positions]), [[0, 0], [0, 1], [1, 0]]);
});

test("without an expected type, a constructor's instance is read from a position argument", async t => {
  const { get } = await cases(t, "instance_from_position");
  assert.equal(get("prepend").type, "(List(N) → List(N))");
});

test("second review: shape errors are reported where the source writes them", async t => {
  const { source, get } = await cases(t, "shape_errors");
  assert.equal(get("Negative").errorStart, source.indexOf("x : Negative"));
  // A boundary with a composition, refused by the kernel (Q3), at its constructor.
  assert.equal(get("Composed").errorStart, source.indexOf("s : trans"));
});

test("second review: inspection shows no marker, and only the result position's words are keywords", async t => {
  const { program } = await cases(t, "no_marker");
  assert.deepEqual(program.inspect("inductive_no_marker__n").extensions, []);
  const { headerWordAt } = await import("../web/source-tokens.mjs");
  const header = "inductive T(x : type) : prop { a; }";
  assert.equal(headerWordAt(header, header.indexOf("type"), "type"), false, "a parameter's type is a name");
  assert.equal(headerWordAt(header, header.indexOf("prop"), "prop"), true);
});

test("third review: a path lambda at a point is contracted in constructor types", async t => {
  const { program } = await cases(t, "path_lambda");
  const shape = signature(program, "path_lambda", "P").constructors;
  assert.deepEqual(shape.map(c => [c.data, c.positions]), [[0, 0], [0, 1], [0, 0]], "s's argument is a position");
});

test("fourth review: normalized views keep no marker", async t => {
  const { program } = await cases(t, "projections");
  assert.deepEqual(program.inspect("inductive_projections__through", { normalize: true }).extensions, []);
});

// V31: trunc(-1) is prop.
test("V31: with the path notation's minus sign, trunc(-1) is prop", async t => {
  const { program } = await cases(t, "trunc_minus_one");
  assert.equal(signature(program, "trunc_minus_one", "Tr").modifier, 1);
});

// The H1 specification's 6.5: a declared type's signature, and the clause
// type its eliminator asks for each constructor, for a motive P over the type
// at its own parameters. The CLI's inspect and the workbench show this view.
test("inspection: a declared type's constructors and its eliminator's clause types", async t => {
  const { program } = await cases(t, "inspection");
  // The fourth review of #74: the first inspection computes the eliminator's
  // clause types in a kernel transaction, and rolls it back.
  const nodes = program.kernel.arena().nodes;
  const circle = program.signatureView("inductive_inspection__S1");
  assert.equal(program.kernel.arena().nodes, nodes);
  // The sort prints by its name: a variable named S1 would print as its stem.
  assert.deepEqual(circle.constructors.map(c => `${c.name} : ${c.type}`), ["base : S1", "loop : base = base"]);
  assert.equal(circle.eliminator.motive, "P : S1 -> U");
  assert.deepEqual(circle.eliminator.clauses.map(c => `${c.name} : ${c.type}`), [
    "base_case : P(base)",
    // A dependent path type prints as the source writes it.
    "loop_case : PathP(fun (i : Interval) => P(loop @ i), base_case, base_case)"]);
  const truncation = program.signatureView("inductive_inspection__Tr");
  assert.deepEqual(truncation.eliminator.clauses.map(c => c.constructor), ["point", "Tr.squash"]);
  // The motive's universe avoids the parameter's name. Tr's universe is
  // erased, which an instance does not carry: it prints as __U.
  assert.equal(truncation.eliminator.motive, "P : Tr(__U, A) -> V");
  assert.equal(truncation.eliminator.clauses[1].type, "forall x : Tr(__U, A). forall x1 : Tr(__U, A). forall x2 : P(x). "
    + "forall x3 : P(x1). PathP(fun (i : Interval) => P(Tr.squash(x, x1) @ i), x2, x3)");
  // A recorded universe parameter by its name in the declaration.
  assert.deepEqual(program.signatureView("inductive_inspection__Pointed").recorded, ["U"]);
  assert.equal(program.signatureView("inductive_inspection__nothing"), null);
});


// The first review of #74: names in the view are never ambiguous, clause
// types print whole, and inspecting again leaves nothing behind.
test("inspection: names are distinct, clause types whole, and repeated inspection keeps no state", async t => {
  const { program } = await cases(t, "inspection_names");
  // A binder named as the type is shown apart from it.
  assert.deepEqual(program.signatureView("inductive_inspection_names__C").constructors.map(c => c.type), ["forall C1 : U0. C1 -> C"]);
  // The motive is not named as a type the clauses mention, nor as a parameter.
  const d = program.signatureView("inductive_inspection_names__D").eliminator;
  assert.equal(d.motive, "Q : D -> U");
  assert.deepEqual(d.clauses.map(c => `${c.name} : ${c.type}`), ["d_case : forall x : P. Q(d(x))"]);
  const e = program.signatureView("inductive_inspection_names__E").eliminator;
  assert.ok(!["P", "Q", "M", "R", "P_"].includes(e.motive.split(" ")[0]), e.motive);
  // A groupoid's squash clause, whole: its boundary comes last.
  const squash = program.signatureView("inductive_inspection_names__G").eliminator.clauses.at(-1).type;
  assert.ok(!squash.includes("…") && squash.length > 400, squash);
  assert.match(squash, /PathP\(fun \(i : Interval\) => .*\)$/);
  // Inspecting again names no new symbols.
  program.signatureView("inductive_inspection_names__Tr");
  const sizes = () => [program.kernel.names.size, program.kernel.symbolNames.size];
  const before = sizes();
  for (let i = 0; i < 3; i++) program.signatureView("inductive_inspection_names__Tr");
  assert.deepEqual(sizes(), before);
});


// The fifth review of #74: a generated name prints as itself after every
// round of suffixes. P__ printed as nothing, as the display reads __ as a
// module's separator: the motive vanished from its clause, and U__ left the
// universe blank. After one underscore, names take a letter.
test("inspection: generated names print as themselves after every round of suffixes", async t => {
  const { program } = await cases(t, "generated_names");
  const e = program.signatureView("inductive_generated_names__E").eliminator;
  assert.equal(e.motive, "P_a : E(P, Q, M, R, P_, Q_, M_, R_) -> U");
  assert.equal(e.clauses[0].type, "P_a(e)");
  assert.equal(program.signatureView("inductive_generated_names__F").eliminator.motive, "P : F(U, V, W, X, Y, V_, W_, X_, Y_) -> U_a");
  assert.deepEqual(program.signatureView("inductive_generated_names__D").eliminator.clauses.map(c => c.name), ["c_case", "d_case"]);
});


// The sixth review of #74: a parameter named a__P prints as P, as the
// display shows the part after a module's separator; the motive was named P
// too, and its clause read forall x : P. P(d(x)). Names are new to every form
// a name prints in.
test("inspection: generated names avoid the printed form of every name", async t => {
  const { program } = await cases(t, "printed_forms");
  const view = program.signatureView("inductive_printed_forms__D");
  assert.equal(view.eliminator.motive, "Q : D(P) -> U");
  assert.equal(view.eliminator.clauses[0].type, "forall x : P. Q(d(x))");
});


// The second review of #74: one naming for the whole view, and the
// generated constructor as the source writes it.
test("inspection: a parameter has one name in the whole view, and T.squash is distinct from squash", async t => {
  const { program } = await cases(t, "one_parameter_name");
  const view = program.signatureView("inductive_one_parameter_name__T");
  const parameter = /^P : T\((\w+)\) -> U$/.exec(view.eliminator.motive)?.[1];
  assert.ok(parameter && parameter !== "c", view.eliminator.motive);
  assert.equal(view.constructors[0].type, `${parameter} -> T`);
  assert.equal(view.eliminator.clauses[0].type, `forall x : ${parameter}. P(c(x))`);
  const squashes = program.signatureView("inductive_one_parameter_name__S");
  assert.deepEqual(squashes.constructors.map(c => c.name), ["squash", "S.squash"]);
  assert.equal(squashes.eliminator.clauses[0].type, "P(squash)");
  assert.match(squashes.eliminator.clauses[1].type, /P\(S\.squash\(x, x1\) @ i\)/);
  // Any display: a variable whose name is a printed label is numbered apart.
  const { T } = await import("../web/translator/core.mjs");
  const constructor = T.constructor(0, T.sort("inductive_one_parameter_name__T"), "c");
  assert.equal(program.checker.displayText(T.app(T.app(T.variable("f"), T.variable("c")), constructor)), "f(c1, c)");
});


// The display shows an assumption by its label, and the view's names do not
// avoid those labels: no declared type mentions an assumption. The kernel
// admits a signature only from closed judgements (the H1 specification's
// 5.2), and the lowering refuses an assumption before it gets there: in a
// parameter, in a constructor's argument, or in a definition one of them
// uses, naming it, where the source writes it, and nothing is admitted.
test("inspection: no declared type mentions an assumption, so the view has no assumption's label to avoid", async t => {
  const { source, program, get } = await cases(t, "assumptions");
  for (const [name, text] of [["InParameter", "t : Truncate"], ["InGeneric", "t : Truncate"], ["InArgument", "t : Truncate"],
    ["InDefinition", "t : ExcludedMiddle"], ["InResult", "Truncate(U0, Nat) -> InResult"]]) {
    assert.ok(get(name).reason.endsWith(` at ${at(source, text, `inductive ${name}`)}`), `${name}: ${get(name).reason}`);
    assert.equal(program.signatureView(`inductive_assumptions__${name}`), null, name);
  }
  assert.equal(program.signatureView("inductive_assumptions__Clear").eliminator.motive, "P : Clear -> U");
});
