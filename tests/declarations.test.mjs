import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { mkdtemp, readFile, rm, writeFile } from "node:fs/promises";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import createCubical from "../web/dist/cubical.mjs";
import { parse } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { observeTestCases } from "../web/cubist/test-pragmas.mjs";
import { listedReader } from "../web/module-resolution.mjs";
import { moduleListing } from "../web/module-listing.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { ReplSession } from "../web/repl-session.mjs";
import { checkProgram, checkTestModule } from "./check-program.mjs";

test("removed theorem declarations are rejected in both source forms", () => {
  for (const source of [
    "theorem identity(A : U0, x : A) = x;",
    "theorem identity : forall A : U0. A -> A { intro A; intro x; exact x; }",
  ]) {
    assert.throws(() => parse(source), /Expected a declaration or directive/);
    assert.throws(() => formatCubist(source), /Expected a declaration or directive/);
  }
});

test("axiom and opaque are not declarations, and imports come first", () => {
  assert.throws(() => parse("axiom assumed : UNat;"), /Expected a declaration or directive: def, computable def/);
  assert.throws(() => parse("opaque def boxed := 0;"), /Expected a declaration or directive: def, computable def/);
  assert.throws(() => parse("def zero_again := 0;\nimport primes;"), /^Error: Imports must come before declarations\.$/);
  // `axiom` starts an expression and is reserved; `opaque` is an ordinary name.
  assert.throws(() => parse("def axiom(n : UNat) := n;"),
    /^Error: axiom is reserved, as a keyword or a built-in type of the language; pick another name\.$/);
  assert.equal(parse("def opaque(n : UNat) := n;").declarations[0].name.text, "opaque");
});

// def Name := axiom Statement; (docs/roadmaps/hott/h1-truncation-migration.md).
test("an axiom is the whole value of a top-level definition without parameters", () => {
  const [lem, stated] = parse("def LEM := axiom ExcludedMiddle;\ndef Stated := axiom forall A : U0. A -> A;").declarations;
  assert.deepEqual([lem.name.text, lem.value.kind, lem.value.statement.name], ["LEM", "axiom", "ExcludedMiddle"]);
  assert.equal(stated.value.statement.kind, "forall");
  for (const source of ["def X(A : U0) := axiom A;", "def X{{U < UU0}} := axiom U;", "def X : U0 := axiom Unit;",
    "def X := (axiom Unit);", "def X := fun (x : Unit) => axiom Unit;", "section (A : U0) { def X := axiom A; }",
    "def X : Unit { exact axiom Unit; }"])
    assert.throws(() => parse(source), error => error.offset === source.indexOf("axiom")
      && error.message === "An axiom is the whole value of a top-level definition without parameters: def Name := axiom Statement;", source);
  // Excluded middle and choice are the library's definitions, not reserved words.
  assert.equal(parse("def LEM := tt;\ndef Choice(LEM : Unit) := LEM;").declarations.length, 2);
});

// `print(evaluate|typeof|inspect(term));` is a top-level directive; `print`,
// `typeof`, `inspect` and `witness` are reserved names.
test("print directives show evaluate, typeof, inspect or witness of a term", () => {
  const { directives } = parse("print(evaluate(2));\nprint(typeof(id));\nprint(inspect(id(0)));\nprint(witness(t));");
  assert.deepEqual(directives.map(d => [d.kind, d.show]), [["print", "evaluate"], ["print", "typeof"], ["print", "inspect"], ["print", "witness"]]);
  assert.deepEqual(directives.map(d => d.start), [0, 20, 39, 62]);
  assert.throws(() => parse("print(normalize(2));"), /^Error: print shows evaluate\(term\), typeof\(term\), inspect\(term\) or witness\(term\)\.$/);
  assert.throws(() => parse("print(evaluate(2);"), /Expected '\)'/);
  assert.throws(() => parse("print;"), /Expected a declaration or directive: def, computable def, inductive, evaluate, print/);
  assert.throws(() => parse("def print(n : UNat) := n;"), /print is reserved/);
});

test("a box lowers to comp or fill, with a face(…) or face_when(…) for each wall", () => {
  const [joined] = parse("def j(A : U0, x : A, p : x = x) : x = x := path i => compose k in A from p @ i { on i = 0 => x; on i = 1 or i = 0 => x; };").declarations;
  // A value after a stated type is the body's exact.
  const box = (joined.value ?? joined.body[0].value).body;
  assert.equal(box.fn.name, "comp");
  assert.deepEqual(box.args.slice(2).map(wall => wall.fn.name), ["face", "face_when"]);
  assert.equal(box.args[0].kind, "lambda");
  const [filled] = parse("def f(A : U0, x : A, p : x = x, t : Interval) : A := fill k in A from p @ t at t { on t = 0 => x; };").declarations;
  assert.equal((filled.value ?? filled.body[0].value).fn.name, "fill");
  // A face is a formula of equations, and compose is reserved.
  assert.throws(() => parse("def j(A : U0, x : A, p : x = x) : x = x := path i => compose k in A from p @ i { on i => x; };"),
    /^Error: A wall's face is a formula of equations i = 0 and i = 1, with and and or, as on i = 0 or j = 1 => …\.$/);
  // A face's equation is a coordinate's: a carrier, =[T], is refused, not dropped.
  const carried = "def identity(A : U0, x : A) : x = x := path i => compose j in A from x { on i =[unbound_type] 0 => x; on i = 1 => x; };";
  assert.throws(() => parse(carried), error => /^A wall's face is a formula of equations/.test(error.message)
    && error.offset === carried.indexOf("unbound_type"));
  assert.throws(() => parse("def j(A : U0, x : A, p : x = x) : x = x := path i => compose k in A from p @ i { on i = 0 => x;"), /Expected '}' to close the box\./);
  assert.throws(() => parse("def compose(n : UNat) := n;"), /compose is reserved/);
});

test("left and right, a sum's injections, are reserved: no binder takes them, while injections and sum patterns stay", () => {
  for (const source of ["def h(left : UNat) := left;", "def k(p : UNat) : UNat { let right := p; exact right; }",
    "def m(f : UNat -> UNat) := fun (left : UNat) => f(left);", "def left := 0;",
    // A bare left in a pattern would be a variable, which catches every
    // value (#186's review): it is refused, alone, beside another value's
    // pattern, as an argument, with coordinates and in a match statement.
    "def f(n : UNat) : UNat := match n { left => left; };", "def f(n : UNat) : UNat := match n { right => 0; };",
    "def f(n, m : UNat) : UNat := match n, m { zero, left => 0; succ(k), _ => k; };",
    "def f(n : UNat) : UNat := match n { zero => 0; succ(left) => left; };",
    "def f(x : Unit or UNat) : UNat := match x { left @ i => 0; };",
    "def f(n : UNat) : UNat { match n { right => { exact right; } } }"])
    assert.throws(() => parse(source), /^Error: (left|right) is reserved, as a keyword or a built-in type of the language; pick another name\.$/);
  parse("def f(x : Unit or UNat) : UNat := match x { left u => 0; right n => n; };");
  parse("def g(x : Unit or UNat) : UNat := match x { left(u) => 0; right(n) => n; };");
  parse("def g(x : (Unit or UNat) or Unit) : UNat := match x { left(right(n)) => n; left(left(u)) => 0; right(u) => 0; };");
  parse("def i : Unit or UNat := left(tt);");
  // A historical source may still bind them (web/cubist/legacy-syntax.mjs).
  parse("def h(left : UNat) := left;", false, { bindable: ["left"] });
});

test("typed, the ascription, is reserved: no binder takes it, while typed(T, e) stays", () => {
  for (const source of ["def typed(n, m : UNat) : UNat := n;", "def h(typed : UNat) := typed;",
    "def k(p : UNat) : UNat { let typed := p; exact typed; }", "def m := fun (typed : UNat) => typed;"])
    assert.throws(() => parse(source), /^Error: typed is reserved, as a keyword or a built-in type of the language; pick another name\.$/);
  parse("def n := typed(UNat, 0);");
  parse("def h(typed : UNat) := typed;", false, { bindable: ["typed"] });
});

// The definitions are cubist-tests/declarations_definitions.cubist, whose
// comments state the refusal (tests/cubist-tests.test.mjs).
test("definitions expose their checked bodies, and a refused one admits nothing", async t => {
  const { program } = await checkTestModule(t, "declarations_definitions");
  const view = program.inspect("declarations_definitions__identity_proof");
  assert.equal(view.folded.reference.name, "declarations_definitions__identity_proof");
  assert.equal(view.folded.expression.tag, "Lam");
  assert.equal(view.statement.parameters.length, 0);
  assert.equal(program.inspect("declarations_definitions__identity").folded.reference, undefined);
  assert.equal(program.kernel.definitions.has("declarations_definitions__false_claim"), false);
});

// The axioms are cubist-tests/declarations_axioms.cubist, whose comments
// state the refusals (tests/cubist-tests.test.mjs).
test("an axiom is one assumption of its family's closed body, shared by its uses and listed by its label", async t => {
  const { program, result } = await checkTestModule(t, "declarations_axioms");
  const binding = "declarations_axioms__Shift", get = name => result.outputs.find(output => output.name === name);
  // The definition names the assumption, a context entry and no kernel definition.
  assert.equal(program.kernel.definitions.has(binding), false);
  assert.equal(program.checker.libraryAssumptions.get("declarations_axioms::Shift")?.name, binding);
  assert.equal(result.assumptionLabels[binding], "declarations_axioms::Shift");
  for (const name of ["Shift", "shifted", "shift_large", "shift_again"]) assert.deepEqual(get(name).axioms, [binding], name);
  // Its type closes the family's body, not the family's own type, U < UU0 -> next(U).
  const type = program.checker.assumptions.get(binding);
  assert.deepEqual([type.tag, type.body.tag, type.body.domain.tag], ["LPi", "Pi", "U"]);
  const view = program.inspect(binding);
  assert.deepEqual(view.axioms, [binding]);
  assert.equal(view.symbols[binding].kind, "axiom");
  assert.equal(view.symbols[binding].name, "declarations_axioms::Shift");
  // A type is assumed as it is.
  assert.equal(program.checker.assumptions.get("declarations_axioms__Unknown").tag, "Sort");
});

// Sources given by module name, each module importing nothing it is not given.
const inMemory = modules => {
  const sources = new Map(Array.isArray(modules) ? modules : Object.entries(modules));
  return async name => sources.get(name) ?? null;
};
const labelsOf = (result, output) => [...new Set(output.axioms.map(name => result.assumptionLabels[name] ?? name))].sort();

// A declaration's identity joins its module's name and its own with __, so
// a::b__c and a__b::c meet in a__b__c. Whichever kinds the two declarations
// are, and in either order, the later is refused, and neither qualified name
// reads the other's value: an axiom stays tracked (#317's review, finding 1).
test("two modules' declarations that would share one identity: the later is refused", async t => {
  const module = await createCubical();
  const clash = /^(a::b__c and a__b::c|a__b::c and a::b__c) would be one identity, a__b__c: rename one of them\./;
  for (const [modules, imports, refused, uses] of [
    [{ a: "def b__c := axiom Unit;", a__b: "def c := tt;" }, ["a", "a__b"], "a__b__c",
      { "a::b__c": /depends on non-computing assumptions: a::b__c/, "a__b::c": /a__b declares no c/ }],
    [{ a: "def b__c := axiom Unit;", a__b: "def c := tt;" }, ["a__b", "a"], "a__b__c",
      { "a::b__c": /a declares no b__c/, "a__b::c": true }],
    [{ a: "inductive T { b__c; }", a__b: "def c := axiom Unit;" }, ["a__b", "a"], "a__T",
      { "a::b__c": /a declares no b__c/, "a__b::c": /depends on non-computing assumptions: a__b::c/ }],
    [{ a: "inductive T { b__c; }", a__b: "import a;\ndef c := axiom T;" }, ["a", "a__b"], "a__b__c",
      { "a::b__c": true, "a__b::c": /a__b declares no c/ }],
    [{ a: "inductive b__c { k; }", a__b: "def c := tt;" }, ["a", "a__b"], "a__b__c",
      { "a::b__c": true, "a__b::c": /a__b declares no c/ }],
  ]) {
    const uses_ = Object.keys(uses).map((name, index) => `computable def use_${index} := ${name};`);
    const source = [...imports.map(name => `import ${name};`), ...uses_].join("\n");
    const { result } = await checkProgram(t, source, { module, reader: inMemory(modules) });
    const failed = result.imports.find(output => output.binding === refused);
    assert.match(failed?.reason ?? "", clash, JSON.stringify(modules));
    for (const [index, expected] of Object.values(uses).entries()) {
      const output = result.outputs.find(item => item.name === `use_${index}`);
      if (expected === true) assert.ok(output.verified, output.reason);
      else assert.match(output.reason ?? "", expected, `${JSON.stringify(modules)}: ${Object.keys(uses)[index]}`);
    }
  }
  // An evaluation cannot compute through the identity either.
  const { program } = await checkProgram(t, "import a;\nimport a__b;\nevaluate a::b__c expecting tt;",
    { module, reader: inMemory({ a: "def b__c := axiom Unit;", a__b: "def c := tt;" }) });
  assert.match(program.gaps.find(gap => gap.directive)?.reason ?? "", /depends on non-computing assumptions: a::b__c/);
});

// The continuum hypotheses will be assumed so (h1-truncation-migration.md,
// "Continuum hypotheses"); cubist-tests/continuum_axioms.cubist assumes them
// in a module of its own, which states every refusal in its comments.
test("a module assumes the continuum hypotheses, and every result that uses one lists it", async t => {
  const { program, result } = await checkTestModule(t, "continuum_axioms");
  const used = name => labelsOf(result, result.outputs.find(output => output.name === name));
  assert.deepEqual(used("CH"), ["continuum_axioms::CH"]);
  assert.deepEqual(used("ch_from_gch"), ["continuum_axioms::GCH"]);
  for (const name of ["both", "at_zero"]) assert.deepEqual(used(name), ["continuum_axioms::CH", "continuum_axioms::GCH"], name);
  // One entry generic over U < UU0, whose body is the statement at U.
  const type = program.checker.assumptions.get("continuum_axioms__CH");
  assert.deepEqual([type.tag, type.body.tag], ["LPi", "Pi"]);
  assert.match(result.outputs.find(output => output.name === "computed").reason,
    /^This computable declaration depends on non-computing assumptions: continuum_axioms::CH\./);
});

// An axiom's assumption never takes a binder's name: an earlier binder's
// generated name can spell the axiom's identity, main__A1 here, and the
// assumption then takes a fresh name, still listed and inspected as the
// axiom (#317's review round 2, finding 2).
test("an axiom whose identity an earlier binder spells takes a fresh assumption name", async t => {
  const { program, result } = await checkProgram(t, "def F(main__A : Unit) : Unit := main__A;\ndef A1 := axiom Unit;\ndef use_ := A1;",
    { module: await createCubical(), reader: inMemory({}) });
  const assumption = program.checker.axioms.get("main__A1");
  assert.equal(program.checker.definitionViews.get("main__F").term.name, "main__A1");
  assert.notEqual(assumption, "main__A1");
  for (const name of ["A1", "use_"]) assert.deepEqual(result.outputs.find(output => output.name === name).axioms, [assumption], name);
  assert.deepEqual(labelsOf(result, result.outputs.find(output => output.name === "use_")), ["main::A1"]);
  assert.deepEqual(program.inspect("main__A1").axioms, [assumption]);
});

// A rule names its declaration by identity, not spelling: two modules'
// axioms spelled alike register two hlevel rules, as two definitions do.
test("hlevel rules that name axioms are registered by the axiom's identity", async t => {
  const fallback = sourceReader(), modules = inMemory({ m1: "import hlevels;\ndef P := axiom IsProp(U0, Unit);\nhlevel_rule P;",
    m2: "import hlevels;\ndef P := axiom IsProp(U0, Void);\nhlevel_rule P;" });
  const { program, result } = await checkProgram(t, "import m1;\nimport m2;\ndef unit_prop : IsProp(U0, Unit) { hlevel; }",
    { module: await createCubical(), reader: async (name, importer) => await modules(name) ?? fallback(name, importer) });
  assert.deepEqual([...program.simpRegistries.get("main").hlevel.keys()].sort(), ["m1__P", "m2__P"]);
  assert.deepEqual(result.outputs[0].axioms, ["m1__P"]);
});

// Only the library's own classical_axioms, read from library/, names its
// axioms LEM and Choice; a module of that name from anywhere else, or edited,
// is labelled as any other, so it cannot pass for them (finding 2).
test("bare axiom labels need the library's own module, in the command line, the browser and the REPL", async t => {
  const module = await createCubical();
  const path = fileURLToPath(new URL("../library/classical_axioms.cubist", import.meta.url));
  const library = await readFile(path, "utf8");
  const forged = "# test(forged) # expect_axioms([LEM])\ndef LEM := axiom Void;\ndef contradiction : Void := LEM;\n";
  const browser = () => listedReader(moduleListing, async file => readFile(fileURLToPath(new URL(`../${file}`, import.meta.url)), "utf8"),
    "classical_axioms", "library");
  for (const [reader, text, labels] of [
    [sourceReader({ path }), library, ["Choice", "LEM"]],
    [browser(), library, ["Choice", "LEM"]],
    [sourceReader({ path }), forged, ["classical_axioms::LEM"]],
    [browser(), forged, ["classical_axioms::LEM"]],
    [sourceReader(), forged, ["classical_axioms::LEM"]],
    [inMemory({}), forged, ["classical_axioms::LEM"]],
  ]) {
    const { program, result } = await checkProgram(t, text, { module, reader, name: "classical_axioms", options: { testMode: true } });
    assert.deepEqual([...new Set(result.outputs.flatMap(output => labelsOf(result, output)))].sort(), labels);
    if (text === forged) assert.deepEqual(observeTestCases(program, result).cases[0].failures[0], "Unknown checked assumption LEM.");
  }
  // An import reads the library's module, as a REPL entry's does.
  const { result } = await checkProgram(t, "import classical_axioms;\ndef excluded := LEM(U0);", { module });
  assert.deepEqual(labelsOf(result, result.outputs[0]), ["LEM"]);
});

// An axiom's statement is read through its module's imports, so a bare label
// needs the whole import closure to be the library's: classical_axioms as
// library/ holds it, over an edited h1_truncation that the session already
// holds, states a forged LEM, which is labelled as any other (#317's review
// round 2, finding 1).
test("a library axiom whose module reads an edited library module is labelled as any other", async t => {
  const module = await createCubical(), path = fileURLToPath(new URL("../library/h1_truncation.cubist", import.meta.url));
  const library = await readFile(path, "utf8"), edited = "import hlevels;\ndef Trunc(U < UU0, A : U) : U := Void;\n";
  const browser = () => listedReader(moduleListing, async file => readFile(fileURLToPath(new URL(`../${file}`, import.meta.url)), "utf8"),
    "h1_truncation", "library");
  for (const [reader, base, label] of [[sourceReader({ path }), edited, "classical_axioms::LEM"], [browser(), edited, "classical_axioms::LEM"],
    [sourceReader({ path }), library, "LEM"]]) {
    const program = new CubicalProgram(module, reader, {});
    t.after(() => program.dispose());
    await program.check(base, "h1_truncation");
    const repl = new ReplSession(program, { base: "h1_truncation" });
    const results = await repl.run(`import classical_axioms;\ndef excluded : ExcludedMiddle(U0) := LEM(U0);`);
    assert.deepEqual(results.map(result => `${result.kind}: ${result.text}`).at(-1), `info: excluded assumes ${label}`);
  }
});

// Every axiom of a library module, read from library/, is listed by its
// bare name (the user's decision of 2026-10-26); the same module from
// anywhere else is listed by its module and name. Module names are user
// text: one named as an object's property reaches no prototype (finding 5).
test("a library module's axioms take their bare names, and the same module elsewhere its qualified ones", async t => {
  const directory = await mkdtemp(join(tmpdir(), "cubist-axiom-modules-"));
  t.after(() => rm(directory, { recursive: true, force: true }));
  const sources = [["constructor", "def X := axiom Unit;\n"], ["toString", "def Y := axiom Unit;\n"]];
  const files = new Map();
  for (const [name, source] of sources) {
    await writeFile(join(directory, `${name}.cubist`), source);
    files.set(`library/${name}`, join(directory, `${name}.cubist`));
  }
  const module = await createCubical(), main = "import constructor;\nimport toString;\ndef both : Unit and Unit := (X, Y);";
  for (const [reader, labels] of [[sourceReader({ files }), ["X", "Y"]], [inMemory(Object.fromEntries(sources)), ["constructor::X", "toString::Y"]]]) {
    const { result } = await checkProgram(t, main, { module, reader });
    assert.deepEqual(result.imports.map(output => [output.binding, labelsOf(result, output)]),
      [["constructor__X", [labels[0]]], ["toString__Y", [labels[1]]]]);
    assert.deepEqual(labelsOf(result, result.outputs[0]), labels);
  }
});
