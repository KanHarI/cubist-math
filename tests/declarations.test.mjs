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
  assert.throws(() => parse("axiom assumed : Nat;"), /Expected a declaration or directive: def, computable def/);
  assert.throws(() => parse("opaque def boxed := 0;"), /Expected a declaration or directive: def, computable def/);
  assert.throws(() => parse("def zero_again := 0;\nimport primes;"), /^Error: Imports must come before declarations\.$/);
  // `axiom` and `opaque` are ordinary names elsewhere.
  assert.equal(parse("def axiom(n : Nat) := n;").declarations[0].name.text, "axiom");
  assert.equal(parse("def opaque(n : Nat) := n;").declarations[0].name.text, "opaque");
});

// `print(evaluate|typeof|inspect(term));` is a top-level directive; `print`,
// `typeof` and `inspect` are ordinary names elsewhere.
test("print directives show evaluate, typeof, inspect or witness of a term", () => {
  const { directives } = parse("print(evaluate(2));\nprint(typeof(id));\nprint(inspect(id(0)));\nprint(witness(t));");
  assert.deepEqual(directives.map(d => [d.kind, d.show]), [["print", "evaluate"], ["print", "typeof"], ["print", "inspect"], ["print", "witness"]]);
  assert.deepEqual(directives.map(d => d.start), [0, 20, 39, 62]);
  assert.throws(() => parse("print(normalize(2));"), /^Error: print shows evaluate\(term\), typeof\(term\), inspect\(term\) or witness\(term\)\.$/);
  assert.throws(() => parse("print(evaluate(2);"), /Expected '\)'/);
  assert.throws(() => parse("print;"), /Expected a declaration or directive: def, computable def, inductive, evaluate, print/);
  assert.equal(parse("def print(typeof : Nat) := typeof;").declarations[0].name.text, "print");
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
  // A face is a formula of equations, and compose is a name elsewhere.
  assert.throws(() => parse("def j(A : U0, x : A, p : x = x) : x = x := path i => compose k in A from p @ i { on i => x; };"),
    /^Error: A wall's face is a formula of equations i = 0 and i = 1, with and and or, as on i = 0 or j = 1 => …\.$/);
  // A face's equation is a coordinate's: a carrier, =[T], is refused, not dropped.
  const carried = "def identity(A : U0, x : A) : x = x := path i => compose j in A from x { on i =[unbound_type] 0 => x; on i = 1 => x; };";
  assert.throws(() => parse(carried), error => /^A wall's face is a formula of equations/.test(error.message)
    && error.offset === carried.indexOf("unbound_type"));
  assert.throws(() => parse("def j(A : U0, x : A, p : x = x) : x = x := path i => compose k in A from p @ i { on i = 0 => x;"), /Expected '}' to close the box\./);
  assert.equal(parse("def compose(n : Nat) := compose(n);").declarations[0].name.text, "compose");
});

test("left and right, a sum's injections, are reserved: no binder takes them, while injections and sum patterns stay", () => {
  for (const source of ["def h(left : Nat) := left;", "def k(p : Nat) : Nat { let right := p; exact right; }",
    "def m(f : Nat -> Nat) := fun (left : Nat) => f(left);", "def left := 0;",
    // A bare left in a pattern would be a variable, which catches every
    // value (#186's review): it is refused, alone, beside another value's
    // pattern, as an argument, with coordinates and in a match statement.
    "def f(n : Nat) : Nat := match n { left => left; };", "def f(n : Nat) : Nat := match n { right => 0; };",
    "def f(n, m : Nat) : Nat := match n, m { zero, left => 0; succ(k), _ => k; };",
    "def f(n : Nat) : Nat := match n { zero => 0; succ(left) => left; };",
    "def f(x : Unit or Nat) : Nat := match x { left @ i => 0; };",
    "def f(n : Nat) : Nat { match n { right => { exact right; } } }"])
    assert.throws(() => parse(source), /^Error: (left|right) is reserved, as a keyword or a built-in type of the language; pick another name\.$/);
  parse("def f(x : Unit or Nat) : Nat := match x { left u => 0; right n => n; };");
  parse("def g(x : Unit or Nat) : Nat := match x { left(u) => 0; right(n) => n; };");
  parse("def g(x : (Unit or Nat) or Unit) : Nat := match x { left(right(n)) => n; left(left(u)) => 0; right(u) => 0; };");
  parse("def i : Unit or Nat := left(tt);");
  // A historical source may still bind them (web/cubist/legacy-syntax.mjs).
  parse("def h(left : Nat) := left;", false, { bindable: ["left"] });
});

test("typed, the ascription, is reserved: no binder takes it, while typed(T, e) stays", () => {
  for (const source of ["def typed(n, m : Nat) : Nat := n;", "def h(typed : Nat) := typed;",
    "def k(p : Nat) : Nat { let typed := p; exact typed; }", "def m := fun (typed : Nat) => typed;"])
    assert.throws(() => parse(source), /^Error: typed is reserved, as a keyword or a built-in type of the language; pick another name\.$/);
  parse("def n := typed(Nat, 0);");
  parse("def h(typed : Nat) := typed;", false, { bindable: ["typed"] });
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
