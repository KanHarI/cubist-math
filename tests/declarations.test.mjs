import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { parse } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { checkTestModule } from "./check-program.mjs";

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
