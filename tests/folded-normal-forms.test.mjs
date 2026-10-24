import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { checkProgram } from "./check-program.mjs";
import { sourceText } from "../web/cubical-source-text.mjs";

// The folded normal form (docs/roadmaps/runtime/folded-normal-forms.md),
// through the kernel's JavaScript interface: closed data computes in full,
// and a definition whose weak head is no data stays as written.
const module = await createCubical();
const source = `import rationals;
use unat;

def two_thirds := rationals.(2/3);

def product := unat.(5) * unat.(3);

def numbers := typed(UNat and UNat, (unat.(2) + unat.(2), unat.(7)));

def glued : Glue(UNat) := glue(unat.(1) + unat.(1));

def glued_pair := typed(Glue(UNat) and Unit, (glued, tt));
`;

const folded = (program, name) => {
  const { kernel, checker } = program;
  const expression = checker.checkSyntax({ tag: "DefRef", name: `main__${name}` }, null, new Map(), new Map()).expression;
  return { kernel, checker, expression, folded: kernel.normalizeFolded(expression) };
};

test("a rational literal's folded normal form names its certificate", async t => {
  const { program, verdicts } = await checkProgram(t, source, { module });
  assert.equal(verdicts.two_thirds, true);
  const before = program.kernel.work().querySteps;
  const { checker, folded: result } = folded(program, "two_thirds");
  // Its full normal form is 70M ticks and over a million nodes.
  assert.ok(program.kernel.work().querySteps - before < 1000000);
  const text = checker.displayText(checker.syntax.decode(result, checker.dimensions), 1000, 1000, checker.notation ?? {}, 0);
  assert.equal(text, "class((class((unat.(2), unat.(0))), class((unat.(3), unat.(0))), int_succ_nonzero(unat.(2))))");
});

test("closed data has the same folded and full normal forms", async t => {
  const { program, verdicts } = await checkProgram(t, source, { module });
  // A glued element is data too: glued computes to glue(2) inside the pair.
  for (const name of ["product", "numbers", "glued_pair"]) {
    assert.equal(verdicts[name], true, name);
    const { kernel, expression, folded: result } = folded(program, name);
    assert.ok(kernel.alphaEqual(result, kernel.normalize(expression)), name);
  }
});

test("the folded normal form is asked of derived terms only", async t => {
  const { program } = await checkProgram(t, source, { module });
  const raw = program.kernel.term("Unit", 0);
  assert.throws(() => program.kernel.normalizeFolded(raw), /Normalize a term or type an instruction derived/);
});

// The marks (FN2): !! computes the folded normal form, !!! the full one; an
// exact expected value is compared by the folded normal forms of both sides.
test("!! prints a literal folded, and an exact rational value is compared folded", async t => {
  const { program, result } = await checkProgram(t, `import rationals;
use unat;

print(evaluate(!!rationals.(2/3)));
evaluate rationals.(2/3) expecting rationals.(2/3);
`, { module });
  assert.deepEqual(result.gaps, []);
  assert.deepEqual(result.prints.map(print => print.text), ["class((class((2, 0)), class((3, 0)), int_succ_nonzero(2)))"]);
  // Both sides' full normal forms are 70M ticks each.
  assert.ok(program.kernel.work().querySteps < 10000000n, String(program.kernel.work().querySteps));
});

// Anywhere inside a !! part, under another mark too, and before anything is
// computed: far's first component, 512, is too deep for a full normal form
// (K344), which E486 comes before. Each is located at its own mark, even
// inside parentheses.
test("a !!! inside a !! part is refused, and !!! alone asks for the full normal form", async t => {
  const source = `import unat;
use unat;

def double(n : UNat) := n + n;
def pair_ : UNat and (UNat -> UNat) := (double(3), double);
def far : UNat and (Unit and Unit) := (2 * 256, (tt, tt));
inductive Box {
  box(u : Unit);
}
def boxed : Box := box(tt);
def sided : Unit or Unit := left(tt);
evaluate pair_ expecting !!(6, !!!_);
evaluate pair_ expecting (6, !!!_);
evaluate typed(Unit and Unit, (tt, tt)) expecting !!!(!!(!!!_), _);
evaluate far expecting (!!!_, !!(tt, !!!_));
evaluate pair_ expecting !!(6, (
  !!!_
));
evaluate sided expecting !!left(!!!_);
evaluate boxed expecting !!box(!!!_);
evaluate tt expecting !!typed(Unit, !!!_);
print(evaluate(!!!pair_));
`;
  const { result } = await checkProgram(t, source, { module });
  assert.deepEqual(result.gaps.map(gap => [gap.code, source.slice(gap.start, gap.end)]), Array(7).fill(["E486", "!!!"]));
  assert.deepEqual(result.gaps.map(gap => source.slice(0, gap.start).split("\n").length), [12, 14, 15, 17, 19, 20, 21]);
  assert.deepEqual(result.prints.map(print => print.text), ["(6, fun (n : UNat) => induction n return UNat { zero => n; succ h => succ(h); })"]);
});

// A folded normal form keeps a clause, a motive or a path clause that is a
// definition by its name; the printer applies it to new names, which keep
// apart from the definitions the text shows, and the text reads back at the
// value's type.
test("a folded function by cases prints as source that reads back", async t => {
  const declarations = `import unat;
use unat;

inductive Circle {
  base;
  loop : base = base;
}

inductive Opt(A : U0) {
  none;
  some(x : A);
}

def a(x : Unit) : Unit := x;
def z(s : Unit or Unit) : U0 := Unit;
def Shape(n : UNat) : U0 := Unit;
def Fits(o : Opt(Unit)) : U0 := Unit;
def rev : base = base := path i => loop @ ~i;
def i : base = base := path j => loop @ ~j;
def Twice(o : Opt(Unit)) : U0 := Unit -> Unit;
inductive Two {
  two(x : Unit, y : Unit);
}
def e(o : Opt(Unit)) : Fits(o) := match o as w return Fits(w) { none => tt; some(x) => x; };
def LFits(U < UU0, o : Opt(Unit)) : U0 := Unit;
def le(o : Opt(Unit)) : LFits(U0, o) := match o as w return LFits(U0, w) { none => tt; some(x) => x; };
def Family : U1 := Opt(Unit) -> U0;
def AFits : Family := fun (o : Opt(Unit)) => Unit;
def ae(o : Opt(Unit)) : AFits(o) := match o as w return AFits(w) { none => tt; some(x) => x; };
def families : (Opt(Unit) -> U0) and Unit := (fun (o : Opt(Unit)) => Unit, tt);
def pe(o : Opt(Unit)) : families.1(o) := match o as w return families.1(w) { none => tt; some(y) => y; };
def Types : U1 and Unit := (Opt(Unit) -> U0, tt);
def TFits : Types.1 := fun (o : Opt(Unit)) => Unit;
def pt(o : Opt(Unit)) : TFits(o) := match o as w return TFits(w) { none => tt; some(y) => y; };
def keep(F : U0 -> U1, g : F(Unit)) : F(Unit) := g;
def pk(o : Opt(Unit)) : keep(fun (A : U0) => Opt(A) -> U0, Fits)(o) := match o as w return keep(fun (A : U0) => Opt(A) -> U0, Fits)(w) { none => tt; some(y) => y; };
`;
  const cases = [
    ["(Unit or Unit) -> Unit", "fun (s : Unit or Unit) => match s return Unit { left x => a(x); right y => y; }",
      "fun (s : Unit or Unit) => match s return Unit { left a1 => a(a1); right y => y; }"],
    ["forall s : Unit or Unit. z(s)", "fun (s : Unit or Unit) => match s as w return z(w) { left x => x; right y => y; }",
      "fun (s : Unit or Unit) => match s as z1 return z(z1) { left x => x; right y => y; }"],
    ["forall n : UNat. Shape(n)", "fun (n : UNat) => induction n as k return Shape(k) { zero => tt; succ h => h; }",
      "fun (n : UNat) => induction n as k return Shape(k) { zero => tt; succ h => h; }"],
    ["(Circle -> Circle) and Unit", "(fun (c : Circle) => match c return Circle { base => base; loop @ i => rev @ i; }, tt)",
      "(fun (x : Circle) => match x return Circle { base => base; loop @ i => rev @ i; }, tt)"],
    ["forall o : Opt(Unit). Fits(o)", "fun (o : Opt(Unit)) => match o as w return Fits(w) { none => tt; some(x) => x; }",
      "fun (x : Opt(Unit)) => match x as z return Fits(z) { none => tt; some(x) => x; }"],
    // A new dimension keeps apart from the definition i; an eliminator
    // applied to more than its value keeps the match spelling.
    ["(Circle -> Circle) and Unit", "(fun (c : Circle) => match c return Circle { base => base; loop @ j => i @ j; }, tt)",
      "(fun (x : Circle) => match x return Circle { base => base; loop @ i1 => i @ i1; }, tt)"],
    ["Opt(Unit) -> Unit", "fun (o : Opt(Unit)) => (match o as w return Twice(w) { none => fun (u : Unit) => u; some(x) => fun (u : Unit) => x; })(tt)",
      "fun (o : Opt(Unit)) => (match o as z return Twice(z) { none => fun (u : Unit) => u; some(x) => fun (u : Unit) => x; })(tt)"],
    // A new argument name keeps apart from the clause's earlier one, which
    // its rest no longer mentions; a folded motive's domain is read from its
    // type, where refl gives the function none.
    ["Two -> Unit", "fun (t : Two) => match t return Unit { two(x, y) => a(y); }",
      "fun (x : Two) => match x return Unit { two(x, x1) => a(x1); }"],
    ["e = e", "refl(fun (o : Opt(Unit)) => match o as w return Fits(w) { none => tt; some(x) => x; })",
      "refl(fun (x : Opt(Unit)) => match x as z return Fits(z) { none => tt; some(x) => x; })"],
    // So for a level-polymorphic motive, and one whose type is an alias.
    ["le = le", "refl(fun (o : Opt(Unit)) => match o as w return LFits(U0, w) { none => tt; some(x) => x; })",
      "refl(fun (x : Opt(Unit)) => match x as z return LFits(U0, z) { none => tt; some(x) => x; })"],
    ["ae = ae", "refl(fun (o : Opt(Unit)) => match o as w return AFits(w) { none => tt; some(x) => x; })",
      "refl(fun (x : Opt(Unit)) => match x as z return AFits(z) { none => tt; some(x) => x; })"],
    // And for one that is a definition projected.
    ["pe = pe", "refl(fun (o : Opt(Unit)) => match o as w return families.1(w) { none => tt; some(y) => y; })",
      "refl(fun (x : Opt(Unit)) => match x as z return families.1(z) { none => tt; some(y) => y; })"],
    // And for one whose type is a pair's component, an alias projected.
    ["pt = pt", "refl(fun (o : Opt(Unit)) => match o as w return TFits(w) { none => tt; some(y) => y; })",
      "refl(fun (x : Opt(Unit)) => match x as z return TFits(z) { none => tt; some(y) => y; })"],
    // And for one whose type is a function of types applied, a redex once
    // keep's arguments are substituted.
    ["pk = pk", "refl(fun (o : Opt(Unit)) => match o as w return keep(fun (A : U0) => Opt(A) -> U0, Fits)(w) { none => tt; some(y) => y; })",
      "refl(fun (x : Opt(Unit)) => match x as z return keep(fun (A : U0) => Opt(A) -> U0, Fits, z) { none => tt; some(y) => y; })"],
  ];
  const { result } = await checkProgram(t, declarations + cases.map(([type, value], i) =>
    `def case_${i} : ${type} := ${value};\nprint(evaluate(!!case_${i}));\n`).join(""), { module });
  assert.deepEqual(result.gaps, []);
  assert.deepEqual(result.prints.map(print => print.text), cases.map(([, , shown]) => shown));
  const { result: back } = await checkProgram(t, declarations + cases.map(([type, , shown], i) =>
    `def back_${i} : ${type} := ${shown};\n`).join(""), { module });
  assert.deepEqual(back.gaps, []);
});

// A recovered domain is printed too, so the names around it keep apart from
// it, invented ones and the term's own binders alike: here x is a
// definition, which a binder x would capture.
test("names keep apart from the definitions a recovered domain prints", async t => {
  const declarations = `inductive Tag(A : U0) {
  tag;
}

def x : U0 := Unit;
def Outer(t : Tag(x)) : U0 := Tag(x) -> Unit;
def Inner(t : Tag(x)) : U0 := Unit;
def Fn : U0 := Tag(x) -> Unit;
inductive Circle {
  base;
  loop : base = base;
}
def i : U0 := Unit;
def Around(t : Tag(i)) : U0 := Circle;
def g0 : Tag(i) -> Circle := fun t => match t as v return Around(v) { tag => base; };
`;
  const cases = [
    ["forall t : Tag(x). Outer(t)",
      "fun (t : Tag(x)) => match t as w return Outer(w) { tag => fun (s : Tag(x)) => match s as v return Inner(v) { tag => tt; }; }",
      "fun (x1 : Tag(x)) => match x1 as z return Outer(z) { tag => fun (x1 : Tag(x)) => match x1 as z return Inner(z) { tag => tt; }; }"],
    // The argument x is the term's own binder: it is shown as x1, and the
    // invented name inside keeps apart from that.
    ["forall x : Unit. Fn", "fun (x : Unit) => fun t => match t as v return Inner(v) { tag => x; }",
      "fun (x1 : Unit) => fun (x2 : Tag(x)) => match x2 as z return Inner(z) { tag => x1; }"],
    // So do a universe's binder and a dimension, here apart from the type i.
    ["forall x < UU0. Fn", "fun (x < UU0) => fun t => match t as v return Inner(v) { tag => tt; }",
      "fun (x1 < UU0) => fun (x1 : Tag(x)) => match x1 as z return Inner(z) { tag => tt; }"],
    ["g0 = g0", "path j => fun t => match t as v return Around(v) { tag => loop @ j; }",
      "path j => fun (x : Tag(i)) => match x as z return Around(z) { tag => loop @ j; }"],
  ];
  const { result } = await checkProgram(t, declarations + cases.map(([type, value], i) =>
    `def case_${i} : ${type} := ${value};\nprint(evaluate(!!case_${i}));\n`).join(""), { module });
  assert.deepEqual(result.gaps, []);
  assert.deepEqual(result.prints.map(print => print.text), cases.map(([, , shown]) => shown));
  const { result: back } = await checkProgram(t, declarations + cases.map(([type, , shown], i) =>
    `def back_${i} : ${type} := ${shown};\n`).join(""), { module });
  assert.deepEqual(back.gaps, []);
});

// Two arguments of one name, the first used under the second: each is shown
// apart, and the printed function computes what the original does.
test("a printed function keeps arguments of one name apart and computes alike", async t => {
  const declarations = `import unat;
use unat;

inductive Tag(A : U0) {
  tag;
}

def x : U0 := Unit;
def Fn : U0 := Tag(x) -> UNat;
def Inner(t : Tag(x)) : U0 := UNat;
`;
  const { result } = await checkProgram(t, `${declarations}def sample(x : UNat) : UNat -> Fn {
  let saved := x;
  exact fun (x : UNat) => fun t => match t as v return Inner(v) { tag => saved; };
}
print(evaluate(!!sample));
evaluate sample(0, 1, tag) expecting 0;
`, { module });
  assert.deepEqual(result.gaps, []);
  const [shown] = result.prints.map(print => print.text);
  assert.equal(shown, "fun (x1, x2 : UNat) => fun (x2 : Tag(x)) => match x2 as z return Inner(z) { tag => x1; }");
  const { result: back } = await checkProgram(t, `${declarations}def back : UNat -> UNat -> Fn := ${shown};
evaluate back(0, 1, tag) expecting 0;
`, { module });
  assert.deepEqual(back.gaps, []);
});

// A successor clause whose hypothesis was folded away is applied to a new
// name, under the predecessor: h is the predecessor's, so it takes h1, and
// the printed function computes what the original does.
test("a curried successor clause keeps its new hypothesis apart from the predecessor", async t => {
  const declarations = `import unat;
use unat;

def foo(a, b, c : UNat) : UNat := a + b + c;
`;
  const { result } = await checkProgram(t, `${declarations}def f(n : UNat) : UNat := induction n as h return UNat { zero => 0; succ ih => foo(h, h, ih); };
print(evaluate(!!f));
evaluate f(2) expecting 2;
`, { module });
  assert.deepEqual(result.gaps, []);
  const [shown] = result.prints.map(print => print.text);
  assert.equal(shown, "fun (n : UNat) => induction n as h return UNat { zero => 0; succ h1 => foo(h, h, h1); }");
  const { result: back } = await checkProgram(t, `${declarations}def back : UNat -> UNat := ${shown};
evaluate back(2) expecting 2;
`, { module });
  assert.deepEqual(back.gaps, []);
});

// The kernel-notation view of a normal form keeps a definition kept by name
// apart from a parameter of that name; and the display keeps a binder it
// names apart from a dimension the term names, here z1, which the term
// leaves free: bound again by path z1, the printed text checks.
test("a normal form's views keep binders apart from definitions and dimensions", async t => {
  const declarations = `inductive Opt(A : U0) {
  none;
  some(x : A);
}

def x(A : U0) : U0 := A;
def both(y : U0 -> U0) : (U0 -> U0) and (U0 -> U0) := (x, y);
def f(x : U0 -> U0) : (U0 -> U0) and (U0 -> U0) := both(x);
def F(o : Opt(Unit)) : U0 := Unit;
def familyPath : F = F := refl(F);
def g : Unit -> Opt(Unit) -> Unit := fun (z : Unit) => fun (x : Opt(Unit)) => match x as w return F(w) { none => tt; some(y) => y; };
`;
  const { program, result } = await checkProgram(t, declarations, { module });
  assert.deepEqual(result.gaps, []);
  assert.equal(program.inspect("main__f", { normalize: true }).expressionText, "λ (x′ : (U0 → U0)). (x , x′)");
  const { kernel, checker } = program;
  const domain = checker.syntax.decode(kernel.definition(kernel.definitions.get("main__F")).type).domain, dimensions = new Map([["z1", 0]]);
  const motive = { tag: "PApp", path: { tag: "DefRef", name: "main__familyPath" }, arg: [["z1:1"]] };
  const clauses = [{ tag: "Point" }, { tag: "Lam", name: "y", domain: { tag: "Unit" }, body: { tag: "Var", name: "y" } }];
  const term = { tag: "Lam", name: "z2", domain: { tag: "Unit" }, body: { tag: "Lam", name: "x", domain,
    body: { tag: "App", fn: { tag: "Elim", signature: "main__Opt", motive, clauses }, arg: { tag: "Var", name: "x" } } } };
  const { expression } = checker.checkSyntax(term, null, new Map(), dimensions);
  const normal = checker.syntax.decode(kernel.normalizeFolded(expression), dimensions);
  const shown = "fun (z : Unit) => fun (x : Opt(Unit)) => match x as z2 return (familyPath @ z1)(z2) { none => tt; some(y) => y; }";
  assert.equal(checker.displayText(normal, 1000, 1000), shown);
  assert.equal(checker.displayGoal(new Map(), normal, null, 1000).goal, shown);
  const { result: back } = await checkProgram(t, `${declarations}def back : g = g := path z1 => ${shown};\n`, { module });
  assert.deepEqual(back.gaps, []);
});

// A definition named as a dimension the term or its context names, here i,
// read from a recovered domain, is shown by its value: no source spelling
// tells it from the dimension, which keeps its name. Bound again by path i,
// the text checks. Kernel notation, which is not read back, shows such a
// definition by its kernel name instead.
test("a definition shown by a dimension's name is shown by its value", async t => {
  const declarations = `inductive Tag(A : U0) {
  tag;
}

inductive Circle {
  base;
  loop : base = base;
}

def i : U0 := Unit;
def Around(t : Tag(i)) : U0 := Circle;
def g : Tag(i) -> Circle := fun t => match t as v return Around(v) { tag => base; };
def d0 : U0 := Unit;
def pair_(x : Circle) : U0 and Circle := (d0, x);
def f : pair_(base) = pair_(base) := path j => pair_(loop @ j);
`;
  const { program, result } = await checkProgram(t, declarations, { module });
  assert.deepEqual(result.gaps, []);
  const { kernel, checker } = program;
  // The kernel's bound dimension is d0, as the definition d0 is labeled.
  assert.equal(program.inspect("main__f", { normalize: true }).expressionText, "path(λ d0. (main__d0 , at(loop, d0:1)))");
  // g uses no dimension, but is shown where the context names i.
  const ambient = new Map([["i", 0]]);
  const folded = checker.syntax.decode(kernel.normalizeFolded(checker.checkSyntax({ tag: "DefRef", name: "main__g" }, null, new Map(), ambient).expression), ambient);
  const unused = "fun (x : Tag(Unit)) => match x as z return Around(z) { tag => base; }";
  assert.equal(checker.displayText(folded, 1000, 1000, undefined, 256, ambient), unused);
  assert.equal(checker.displayText(folded, 1000, 1000, undefined, 256, new Map()), unused.replace("Tag(Unit)", "Tag(i)"));
  const domain = checker.syntax.decode(kernel.definition(kernel.definitions.get("main__Around")).type).domain;
  const circle = { tag: "Sort", signature: "main__Circle", parameters: [], levels: [] };
  const loop = { tag: "PApp", path: { tag: "Con", index: 1, sort: circle }, arg: [["i:1"]] };
  const term = { tag: "Lam", name: "x", domain, body: { tag: "App", arg: { tag: "Var", name: "x" },
    fn: { tag: "Elim", signature: "main__Tag", motive: { tag: "DefRef", name: "main__Around" }, clauses: [loop] } } };
  const dimensions = new Map([["i", 0]]);
  const { expression } = checker.checkSyntax(term, null, new Map(), dimensions);
  const normal = checker.syntax.decode(kernel.normalizeFolded(expression), dimensions);
  const shown = "fun (x : Tag(Unit)) => match x as z return Around(z) { tag => loop @ i; }";
  assert.equal(checker.displayText(normal, 1000, 1000), shown);
  assert.equal(checker.displayGoal(new Map(), normal, null, 1000).goal, shown);
  const { result: back } = await checkProgram(t, `${declarations}def back : g = g := path i => ${shown};
def unused : g = g := path i => ${unused};
`, { module });
  assert.deepEqual(back.gaps, []);
});

// The printer's first name for a folded function's argument keeps apart
// from a dimension its body uses: under path x, an eliminator whose clause
// is p @ x takes x1, not x.
test("a name the printer invents keeps apart from the dimensions in scope", () => {
  const sort = { tag: "Sort", signature: "main__N", parameters: [], levels: [] };
  const symbols = { main__N: { name: "N", slots: [], constructors: [{ name: "zero", data: 0, positions: 0, dimensions: 0 }] },
    main__p: { name: "p" }, main__T: { name: "T" } };
  const elim = { tag: "Elim", signature: "main__N", motive: { tag: "Lam", name: "m", domain: sort, body: { tag: "DefRef", name: "main__T" } },
    clauses: [{ tag: "PApp", path: { tag: "DefRef", name: "main__p" }, arg: [["x:1"]] }] };
  assert.equal(sourceText({ tag: "PLam", dim: "x", family: null, body: elim }, symbols),
    "path x => fun (x1 : N) => match x1 return T { zero => p @ x; }");
});

// A !!! inside a !! part is refused before the evaluated term is elaborated:
// a numeral's reader (nat's literal rule) computes, and computes nothing
// here; nor does a part under a constructor, an injection or typed.
test("a !!! inside a !! part is refused before the evaluated literal computes", async t => {
  const { program } = await checkProgram(t, "", { module });
  const kernel = program.kernel;
  let calls = 0;
  for (const query of ["normalize", "normalizeFolded"]) {
    const original = kernel[query].bind(kernel);
    kernel[query] = handle => { calls++; return original(handle); };
  }
  const header = "import nat;\nuse nat;\n\ndef anchor : Unit := tt;\ndef sided : Nat or Unit := right(tt);\n";
  const warm = await program.check(header, "literal_warm", () => {}, { reuseModules: true });
  assert.deepEqual(warm.gaps, []);
  calls = 0;
  const result = await program.check(`${header}evaluate 5 expecting !!(!!!_);
evaluate sided expecting !!left(!!!_);
evaluate typed(Nat and Unit, (5, tt)) expecting !!typed(Nat and Unit, (!!!_, _));
`, "literal_refused", () => {}, { reuseModules: true });
  assert.deepEqual(result.gaps.map(gap => gap.code), ["E486", "E486", "E486"]);
  assert.equal(calls, 0, "no normal form is computed before E486");
});

// An exact value and a pattern's leaf are compared with the value's folded
// normal form by conversion: a and b are distinct definitions of one
// function, so pa and pb fold apart, to (a, 1) and (b, 1).
test("an expected value is compared with a folded normal form by conversion", async t => {
  const source = `import unat;
use unat;

def a(n : UNat) : UNat := n;
def b(n : UNat) : UNat := n;
def c(n : UNat) : UNat := n + 1;
def pa : (UNat -> UNat) and UNat := (a, 1);
def pb : (UNat -> UNat) and UNat := (b, 1);
def pc : (UNat -> UNat) and UNat := (c, 1);
def nested : ((UNat -> UNat) and UNat) and UNat := (pa, 1);
evaluate pa expecting pb;
evaluate nested expecting (pb, _);
evaluate pa expecting pc;
evaluate nested expecting (pc, _);
`;
  const { result } = await checkProgram(t, source, { module });
  assert.deepEqual(result.evaluations.map(evaluation => evaluation.value), ["(a, 1)", "((a, 1), <unevaluated>)"]);
  assert.deepEqual(result.gaps.map(gap => [gap.code, source.slice(0, gap.start).split("\n").length]), [["E326", 13], ["E477", 14]]);
});

// Each caller asks for the normal form its table row in the note assigns:
// an exact value, folded; a witness, full; !! folded and !!! full.
test("exact values fold, and !!! and witness ask for the full normal form", async t => {
  const { program } = await checkProgram(t, "", { module });
  const kernel = program.kernel, asked = [];
  for (const query of ["normalize", "normalizeFolded"]) {
    const original = kernel[query].bind(kernel);
    kernel[query] = handle => { asked.push(query); return original(handle); };
  }
  // Each source a module of its own name, which reuseModules keeps apart.
  let runs = 0;
  const run = async source => {
    asked.length = 0;
    const result = await program.check(`import h1_truncation;\nuse unat;\n${source}`, `routing_${runs++}`, () => {}, { reuseModules: true });
    assert.deepEqual(result.gaps, [], source);
    return [...new Set(asked)];
  };
  assert.deepEqual(await run("evaluate 2 + 2 expecting 4;"), ["normalizeFolded"]);
  assert.deepEqual(await run("evaluate 2 + 2 expecting !!_;"), ["normalizeFolded"]);
  assert.deepEqual(await run("evaluate 2 + 2 expecting !!!_;"), ["normalize"]);
  assert.deepEqual(await run("print(witness(typed(Trunc(U0, UNat), point(3))));"), ["normalize"]);
});

// The term asked for is unfolded even where one step takes it to a stuck
// elimination: f is eta its eliminator, so f(x) steps straight to it, and
// the folded normal form shows that eliminator, as the weak head does; and
// so where f(x) is applied, projected or applied to a dimension, whose
// step takes f(x)'s weak head in steps of its own.
test("the term asked for is unfolded where a definition is eta an eliminator", async t => {
  const { program, verdicts } = await checkProgram(t, `inductive N {
  zero;
  succ(k : N);
}

def f(n : N) := match n return N { zero => zero; succ(k) => k; };

def computes_f := match zero return N -> N { zero => f; succ(k) => f; };

def shift(n : N) := match n return N -> N { zero => fun (m : N) => m; succ(k) => fun (m : N) => k; };

def halves(n : N) := match n return N and N { zero => (zero, zero); succ(k) => (k, k); };

def constant(n : N) := match n return zero = zero { zero => refl(zero); succ(k) => refl(zero); };
`, { module });
  for (const name of ["f", "computes_f", "shift", "halves", "constant"]) assert.equal(verdicts[name], true, name);
  const { kernel, checker } = program;
  const value = name => kernel.definition(kernel.definitions.get(`main__${name}`));
  const domain = checker.syntax.decode(value("f").type).domain, x = { tag: "Var", name: "x" };
  // The root of an application, level application, projection or path
  // application spine.
  const root = handle => {
    let term = checker.syntax.decode(handle, new Map([["i", 0]]));
    while (["App", "LApp", "Fst", "Snd", "PApp"].includes(term.tag)) term = term.fn ?? term.pair ?? term.path;
    return term.tag;
  };
  const at = name => ({ tag: "App", fn: { tag: "DefRef", name: `main__${name}` }, arg: x });
  // f(x) itself, and a match by cases on zero that computes f, applied to x:
  // another eliminator at the root, even of the same kind, is no rebuild.
  const computed = { tag: "App", fn: checker.syntax.decode(value("computes_f").value), arg: x };
  const terms = [at("f"), computed, { tag: "App", fn: at("shift"), arg: x },
    { tag: "Fst", pair: at("halves") }, { tag: "Snd", pair: at("halves") }, { tag: "PApp", path: at("constant"), arg: [["i:1"]] }];
  for (const term of terms) {
    const { expression } = checker.checkSyntax(term, null, new Map([["x", domain]]), new Map([["i", 0]]));
    assert.equal(root(kernel.head(expression)), "Elim", term.tag);
    assert.equal(root(kernel.normalizeFolded(expression)), "Elim", term.tag);
    assert.equal(root(kernel.normalize(expression)), "Elim", term.tag);
  }
  // shift's eliminator stuck on f(x), applied to x: the step rebuilt it in
  // place, its scrutinee reduced, so f(x) stays as written there.
  const shifted = checker.syntax.decode(value("shift").value);
  const eliminator = shifted.tag === "Lam" && shifted.body.tag === "App" ? shifted.body.fn : shifted;
  assert.equal(eliminator.tag, "Elim");
  const stuck = { tag: "App", fn: { tag: "App", fn: eliminator, arg: at("f") }, arg: x };
  const { expression } = checker.checkSyntax(stuck, null, new Map([["x", domain]]), new Map());
  const scrutinee = handle => checker.syntax.decode(handle).fn.arg;
  assert.equal(scrutinee(kernel.normalizeFolded(expression)).fn.tag, "DefRef");
  assert.equal(scrutinee(kernel.normalize(expression)).fn.tag, "Elim");
});

// The folded normal form does not depend on syntax interning. f's
// eliminator, read back and checked again, is f's own node with interning
// and a copy without; applied to box(f(x)) it computes f's eliminator at x,
// which is no rebuild of it in place, in either mode.
test("interning does not change a folded normal form", async t => {
  const shown = [];
  for (const shareSyntax of [true, false]) {
    const program = new CubicalProgram(module, sourceReader(), { collectReferences: false, optimizations: { shareSyntax } });
    t.after(() => program.dispose());
    const result = await program.check(`inductive Box {
  box(g : Unit -> Unit);
}

def f(s : Box) := match s return Unit -> Unit { box(g) => g; };
`, "main");
    assert.deepEqual(result.gaps, []);
    const { kernel, checker } = program, f = kernel.definition(kernel.definitions.get("main__f"));
    const domain = checker.syntax.decode(f.type).domain, value = checker.syntax.decode(f.value);
    const eliminator = value.tag === "Lam" && value.body.tag === "App" ? value.body.fn : value;
    assert.equal(eliminator.tag, "Elim");
    const x = { tag: "Var", name: "x" };
    const boxed = { tag: "App", fn: { tag: "Con", index: 0, sort: domain }, arg: { tag: "App", fn: { tag: "DefRef", name: "main__f" }, arg: x } };
    const term = { tag: "App", fn: { tag: "App", fn: eliminator, arg: boxed }, arg: { tag: "Point" } };
    const { expression } = checker.checkSyntax(term, null, new Map([["x", domain]]), new Map());
    shown.push(checker.displayText(checker.syntax.decode(kernel.normalizeFolded(expression)), 1000, 1000, {}, 0));
  }
  assert.equal(shown[0], shown[1]);
});
