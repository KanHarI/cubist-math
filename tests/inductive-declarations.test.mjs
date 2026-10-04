// `inductive` declarations, work-plan L2.1 (docs/roadmaps/h1-signature-
// specification.md, section 9): the header's result position, lowering to
// the normal form with data before positions, universe classification, the
// least level, uses of the type and its constructors, the kernel's H1 switch
// and the absence of the marker since H1's release (6.4), and the rejections.
// The cases are the cubist-tests/inductive_*.cubist modules, whose comments
// state each refusal, and what each print shows: types, and signatures with
// their eliminators' clause types (tests/cubist-tests.test.mjs). Here, what
// neither shows: markers, assumptions, positions and the kernel's state.
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
test("T2: no result that uses a declared type carries a marker", async t => {
  const { get } = await cases(t, "values");
  for (const name of ["N", "List", "two", "two_is_two", "one_two", "counted"]) {
    assert.deepEqual(get(name).extensions, [], `${name} carries no marker`);
    assert.deepEqual(get(name).axioms, []);
  }
  assert.deepEqual(get("plain").extensions, []);
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

test("fourth review: normalized views keep no marker", async t => {
  const { program } = await cases(t, "projections");
  assert.deepEqual(program.inspect("inductive_projections__through", { normalize: true }).extensions, []);
});

// The H1 specification's 6.5: a declared type's signature, and its
// eliminator's clause types, as the CLI's inspect, the workbench and
// print(inspect(T)) show them. The cases print theirs; a name that is no
// declared type has none.
test("inspection: a name that is no declared type has no signature", async t => {
  const { program } = await cases(t, "inspection");
  assert.equal(program.signatureView("inductive_inspection__nothing"), null);
});

// The fourth review of #74: the first inspection computes the eliminator's
// clause types in a kernel transaction, and rolls it back. The first review:
// inspecting again names no new symbols. Tr is inspected here first.
test("inspection: the first inspection is rolled back, and repeated inspection keeps no state", async t => {
  const { program } = await cases(t, "inspection_names");
  const nodes = program.kernel.arena().nodes;
  assert.ok(program.signatureView("inductive_inspection_names__Tr").eliminator);
  assert.equal(program.kernel.arena().nodes, nodes);
  const sizes = () => [program.kernel.names.size, program.kernel.symbolNames.size];
  const before = sizes();
  for (let i = 0; i < 3; i++) program.signatureView("inductive_inspection_names__Tr");
  assert.deepEqual(sizes(), before);
});

// Any display: a variable whose name is a printed label is numbered apart.
test("a display numbers a variable named as a printed label apart from it", async t => {
  const { program } = await cases(t, "one_parameter_name");
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
});
