import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { cubicalMathTree } from "../web/cubical-notation.mjs";
import { forSource } from "../web/display-naming.mjs";
import { sourceText } from "../web/cubical-source-text.mjs";
import { checkProgram } from "./check-program.mjs";

// The display's naming (web/README.md, "Displaying terms"): no two different
// things show one name where both are in scope. A folded normal form keeps
// definitions under binders (docs/roadmaps/runtime/folded-normal-forms.md),
// so this corpus names its definitions as the display's own stems, the
// names it gives binders (x, z, k, h, a, b) and dimensions (i, j, d0, z1),
// and every case is a function by cases, a lambda chain or a path whose
// folded normal form keeps them where a binder of that name would capture
// them. Each case's printed folded normal form must read back at its type
// and be the same function, by conversion, and compute as it does; and so
// where the context names each of those dimensions. Its kernel-notation view
// must show no definition by the name of a binder around it.

const module = await createCubical();

const declarations = `import unat;
use unat;

inductive Circle {
  base;
  loop : base = base;
}

inductive Opt(A : U0) {
  none;
  some(y : A);
}

inductive Two {
  two(p : Unit, q : Unit);
}

inductive Tag(A : U0) {
  tag;
}

// Named as the display's binder stems.
def x : U0 := Unit;
def z(s : Unit or Unit) : U0 := Unit;
def k(n : UNat) : U0 := Unit;
def h(n : UNat) : UNat := n;
def a(u : Unit) : Unit := u;
def b(u : Unit) : Unit := u;

// Named as the display's dimension names.
def i : base = base := path e => loop @ ~e;
def j : U0 := Unit;
def d0 : U0 := Unit;
def z1 : U0 := Unit;

def foo(m, n, l : UNat) : UNat := m + n + l;
def Shape(n : UNat) : U0 := Unit;
def Fits(o : Opt(Unit)) : U0 := Unit;
def LFits(U < UU0, o : Opt(Unit)) : U0 := Unit;
def Family : U1 := Opt(Unit) -> U0;
def AFits : Family := fun (o : Opt(Unit)) => Unit;
def families : (Opt(Unit) -> U0) and Unit := (fun (o : Opt(Unit)) => Unit, tt);
def Types : U1 and Unit := (Opt(Unit) -> U0, tt);
def TFits : Types.1 := fun (o : Opt(Unit)) => Unit;
def keep(F : U0 -> U1, g : F(Unit)) : F(Unit) := g;
def Twice(o : Opt(Unit)) : U0 := Unit -> Unit;
def Outer(t : Tag(x)) : U0 := Tag(x) -> Unit;
def Inner(t : Tag(x)) : U0 := Unit;
def InnerN(t : Tag(x)) : U0 := UNat;
def Fn : U0 := Tag(x) -> UNat;
def FnU : U0 := Tag(x) -> Unit;
def Around(t : Tag(j)) : U0 := Circle;
def Inside(t : Tag(d0)) : U0 := Unit;
def Beside(t : Tag(z1)) : U0 := Unit;
`;

// Each case: a definition's name and its declaration, and inputs at which
// the printed copy must compute what the original does.
const cases = [
  // A clause folded to a definition named as the branch's stem.
  ["sum_clause", "def sum_clause : (Unit or Unit) -> Unit := fun (s : Unit or Unit) => match s return Unit { left u => a(u); right v => b(v); };"],
  // A motive folded to a definition named as the motive's stem.
  ["sum_motive", "def sum_motive : forall s : Unit or Unit. z(s) := fun (s : Unit or Unit) => match s as w return z(w) { left u => u; right v => v; };"],
  // Induction with folded motives, one named as the predecessor's stem.
  ["nat_motive", "def nat_motive : forall n : UNat. Shape(n) := fun (n : UNat) => induction n as m return Shape(m) { zero => tt; succ q => q; };"],
  ["nat_k", "def nat_k : forall n : UNat. k(n) := fun (n : UNat) => induction n as m return k(m) { zero => tt; succ q => q; };"],
  // A successor clause whose hypothesis folds away, under a predecessor
  // named as the hypothesis' stem, and a definition of that stem inside.
  ["nat_step", "def nat_step(n : UNat) : UNat := induction n as h return UNat { zero => 0; succ ih => foo(h, h, ih); };", [[2, 2], [3, 6]]],
  ["nat_h", "def nat_h(n : UNat) : UNat := induction n as m return UNat { zero => 0; succ ih => foo(h(m), m, ih); };", [[2, 2], [3, 6]]],
  // A clause whose arguments are invented, beside one the term has.
  ["two_clause", "def two_clause : Two -> Unit := fun (t : Two) => match t return Unit { two(p, q) => a(q); };"],
  // A path clause folded to a definition named as the dimension's stem.
  ["path_clause", "def path_clause : (Circle -> Circle) and Unit := (fun (c : Circle) => match c return Circle { base => base; loop @ e => i @ e; }, tt);"],
  // An eliminator as a function, where no type reaches it: its domain is
  // read from its folded motive's type, through applications, levels, an
  // alias, projections and a function of types applied.
  ["fits", "def fits(o : Opt(Unit)) : Fits(o) := match o as w return Fits(w) { none => tt; some(y) => y; };"],
  ["fits_refl", "def fits_refl : fits = fits := refl(fun (o : Opt(Unit)) => match o as w return Fits(w) { none => tt; some(y) => y; });"],
  ["lfits", "def lfits(o : Opt(Unit)) : LFits(U0, o) := match o as w return LFits(U0, w) { none => tt; some(y) => y; };"],
  ["lfits_refl", "def lfits_refl : lfits = lfits := refl(fun (o : Opt(Unit)) => match o as w return LFits(U0, w) { none => tt; some(y) => y; });"],
  ["afits", "def afits(o : Opt(Unit)) : AFits(o) := match o as w return AFits(w) { none => tt; some(y) => y; };"],
  ["afits_refl", "def afits_refl : afits = afits := refl(fun (o : Opt(Unit)) => match o as w return AFits(w) { none => tt; some(y) => y; });"],
  ["pfits", "def pfits(o : Opt(Unit)) : families.1(o) := match o as w return families.1(w) { none => tt; some(y) => y; };"],
  ["pfits_refl", "def pfits_refl : pfits = pfits := refl(fun (o : Opt(Unit)) => match o as w return families.1(w) { none => tt; some(y) => y; });"],
  ["tfits", "def tfits(o : Opt(Unit)) : TFits(o) := match o as w return TFits(w) { none => tt; some(y) => y; };"],
  ["tfits_refl", "def tfits_refl : tfits = tfits := refl(fun (o : Opt(Unit)) => match o as w return TFits(w) { none => tt; some(y) => y; });"],
  ["kfits", "def kfits(o : Opt(Unit)) : keep(fun (A : U0) => Opt(A) -> U0, Fits)(o) := match o as w return keep(fun (A : U0) => Opt(A) -> U0, Fits)(w) { none => tt; some(y) => y; };"],
  ["kfits_refl", "def kfits_refl : kfits = kfits := refl(fun (o : Opt(Unit)) => match o as w return keep(fun (A : U0) => Opt(A) -> U0, Fits)(w) { none => tt; some(y) => y; });"],
  // An eliminator applied to its value and more.
  ["twice", "def twice : Opt(Unit) -> Unit := fun (o : Opt(Unit)) => (match o as w return Twice(w) { none => fun (u : Unit) => u; some(y) => fun (u : Unit) => y; })(tt);"],
  // Recovered domains print definitions named as binders around them.
  ["nested", "def nested : forall t : Tag(x). Outer(t) := fun (t : Tag(x)) => match t as w return Outer(w) { tag => fun (s : Tag(x)) => match s as v return Inner(v) { tag => tt; }; };"],
  ["argument", "def argument : forall x : Unit. FnU := fun (x : Unit) => fun t => match t as v return Inner(v) { tag => x; };"],
  ["leveled", "def leveled : forall x < UU0. FnU := fun (x < UU0) => fun t => match t as v return Inner(v) { tag => tt; };"],
  // A universe binder renamed where its level is used inside, a clause
  // that shows the definition x beside an invented argument, and a binder
  // the term has, named as a definition its body shows.
  ["lev", "def lev : forall x < UU0. forall A : x. A -> FnU := fun (x < UU0) => fun (A : x) => fun (u : A) => fun t => match t as v return Inner(v) { tag => tt; };"],
  ["clause_x", "def clause_x : Opt(Unit) -> U0 := fun o => match o return U0 { none => x; some(y) => x; };"],
  ["bin_x", "def bin_x : forall y : UNat. FnU := fun (y : UNat) => fun t => match t as v return Inner(v) { tag => tt; };"],
  ["chain", "def chain(x : UNat) : UNat -> Fn {\n  let saved := x;\n  exact fun (x : UNat) => fun t => match t as v return InnerN(v) { tag => saved; };\n}", [["0, 1, tag", 0]]],
  // A path whose body prints definitions named as dimensions.
  ["around", "def around0 : Tag(j) -> Circle := fun t => match t as v return Around(v) { tag => base; };\ndef around : around0 = around0 := path e => fun t => match t as v return Around(v) { tag => loop @ e; };"],
  ["inside", "def inside : Tag(d0) -> Unit := fun t => match t as v return Inside(v) { tag => tt; };"],
  ["beside", "def beside : Tag(z1) -> Unit := fun t => match t as v return Beside(v) { tag => tt; };"],
];

const source = declarations + cases.map(([, declaration]) => `${declaration}\n`).join("")
  + cases.map(([name]) => `print(evaluate(!!${name}));\n`).join("");

// The printed folded normal forms, their checked types, and the checker.
const shown = async t => {
  const { program, result } = await checkProgram(t, source, { module });
  assert.deepEqual(result.gaps, []);
  const texts = new Map(cases.map(([name], index) => [name, result.prints[index].text]));
  return { program, texts };
};
const typeOf = (program, name) => program.checker.displayText(program.checker.syntax.decode(
  program.kernel.definition(program.kernel.definitions.get(`main__${name}`)).type), 1000, 1000, undefined, 256, new Map());

test("each folded normal form reads back as the same function, and computes alike", async t => {
  const { program, texts } = await shown(t);
  const back = cases.map(([name, , inputs = []]) => [
    `def back_${name} : ${typeOf(program, name)} := ${texts.get(name)};`,
    `def same_${name} : back_${name} = ${name} := refl(${name});`,
    ...inputs.map(([input, value]) => `evaluate back_${name}(${input}) expecting ${value};\nevaluate ${name}(${input}) expecting ${value};`),
  ].join("\n")).join("\n");
  const { result } = await checkProgram(t, `${source}${back}\n`, { module });
  assert.deepEqual(result.gaps.map(gap => `${gap.name}: ${gap.code} ${gap.reason}`), [], [...texts].map(([name, text]) => `${name}: ${text}`).join("\n"));
});

test("shown where the context names a dimension, each reads back bound by it", async t => {
  const { program } = await shown(t);
  const { kernel, checker } = program;
  const back = [];
  for (const dimension of ["i", "j", "d0", "z1"]) {
    const context = new Map([[dimension, 0]]);
    for (const [name] of cases) {
      const { expression } = checker.checkSyntax({ tag: "DefRef", name: `main__${name}` }, null, new Map(), context);
      const text = checker.displayText(checker.syntax.decode(kernel.normalizeFolded(expression), context), 4000, 4000, undefined, 256, context);
      back.push(`def ${dimension}_${name} : ${name} = ${name} := path ${dimension} => ${text};`);
    }
  }
  const { result } = await checkProgram(t, `${source}${back.join("\n")}\n`, { module });
  assert.deepEqual(result.gaps.map(gap => `${gap.name}: ${gap.code} ${gap.reason}`), []);
});

// In kernel notation, a definition is a name with its binding; it must not
// be spelled as a binder around it is, a term's or a dimension's.
test("a normalized view shows no definition by the name of a binder around it", async t => {
  const { program } = await shown(t);
  const clashes = [];
  for (const [name] of cases) {
    const view = program.inspect(`main__${name}`, { normalize: true });
    const tree = cubicalMathTree(view.expression, view.symbols, 100000, { dimensions: (view.dimensions ?? []).map(([dimension]) => dimension) });
    const walk = (node, bound) => {
      if (!node || typeof node !== "object") return;
      if (Array.isArray(node)) return node.forEach(item => walk(item, bound));
      if (node.kind === "Name" && node.binding && bound.has(node.name)) clashes.push(`${name}: ${node.name}`);
      const inner = typeof node.name === "string" && ["Lambda", "Pi", "Sigma", "LevelPi", "LevelLambda"].includes(node.kind)
        ? new Set([...bound, node.name]) : node.kind === "Scope" ? new Set([...bound, ...node.names]) : bound;
      for (const [key, value] of Object.entries(node)) if (key !== "name") walk(value, key === "body" ? inner : bound);
    };
    walk(tree, new Set());
  }
  assert.deepEqual(clashes, []);
});

// Open terms, as goals and inspections show them: a binder is named apart
// from the dimensions a term names, here z1, which it leaves free; a
// definition named as a dimension of the term or of its context, here i, is
// shown by its value, as no source spelling tells the two apart; and kernel
// notation, not read back, shows such a definition by its kernel name and
// spells a binder apart from the definitions its body shows. Bound again by
// path z1 or path i, each source text checks.
test("open terms keep binders and definitions apart from the dimensions they and their context name", async t => {
  const declarations = `inductive Opt(A : U0) {
  none;
  some(y : A);
}

inductive Tag(A : U0) {
  tag;
}

inductive Circle {
  base;
  loop : base = base;
}

def x(A : U0) : U0 := A;
def both(y : U0 -> U0) : (U0 -> U0) and (U0 -> U0) := (x, y);
def f(x : U0 -> U0) : (U0 -> U0) and (U0 -> U0) := both(x);
def F(o : Opt(Unit)) : U0 := Unit;
def familyPath : F = F := refl(F);
def fam : Unit -> Opt(Unit) -> Unit := fun (z : Unit) => fun (x : Opt(Unit)) => match x as w return F(w) { none => tt; some(y) => y; };
def i : U0 := Unit;
def Around(t : Tag(i)) : U0 := Circle;
def g : Tag(i) -> Circle := fun t => match t as v return Around(v) { tag => base; };
def d0 : U0 := Unit;
def pair_(c : Circle) : U0 and Circle := (d0, c);
def p : pair_(base) = pair_(base) := path j => pair_(loop @ j);
`;
  const { program, result } = await checkProgram(t, declarations, { module });
  assert.deepEqual(result.gaps, []);
  const { kernel, checker } = program;
  assert.equal(program.inspect("main__f", { normalize: true }).expressionText, "λ (x′ : (U0 → U0)). (x , x′)");
  // The kernel's bound dimension is d0, as the definition d0 is labeled.
  assert.equal(program.inspect("main__p", { normalize: true }).expressionText, "path(λ d0. (main__d0 , at(loop, d0:1)))");
  const typeOfDefinition = name => checker.syntax.decode(kernel.definition(kernel.definitions.get(`main__${name}`)).type);
  const folded = (term, dimensions) => checker.syntax.decode(kernel.normalizeFolded(checker.checkSyntax(term, null, new Map(), dimensions).expression), dimensions);
  const both_ = (term, shown) => {
    assert.equal(checker.displayText(term, 1000, 1000), shown);
    assert.equal(checker.displayGoal(new Map(), term, null, 1000).goal, shown);
  };
  // A folded motive beside the dimension z1, which the term names.
  const familyAt = { tag: "PApp", path: { tag: "DefRef", name: "main__familyPath" }, arg: [["z1:1"]] };
  const clauses = [{ tag: "Point" }, { tag: "Lam", name: "y", domain: { tag: "Unit" }, body: { tag: "Var", name: "y" } }];
  const z1 = folded({ tag: "Lam", name: "z2", domain: { tag: "Unit" }, body: { tag: "Lam", name: "x", domain: typeOfDefinition("F").domain,
    body: { tag: "App", fn: { tag: "Elim", signature: "main__Opt", motive: familyAt, clauses }, arg: { tag: "Var", name: "x" } } } }, new Map([["z1", 0]]));
  const z1Shown = "fun (z : Unit, x : Opt(Unit)) => match x as z2 return (familyPath @ z1)(z2) { none => tt; some(y) => y; }";
  both_(z1, z1Shown);
  // The definition i, in a recovered domain, beside the dimension i.
  const circle = { tag: "Sort", signature: "main__Circle", parameters: [], levels: [] };
  const loop = { tag: "PApp", path: { tag: "Con", index: 1, sort: circle }, arg: [["i:1"]] }, ambient = new Map([["i", 0]]);
  const iTerm = folded({ tag: "Lam", name: "x", domain: typeOfDefinition("Around").domain, body: { tag: "App", arg: { tag: "Var", name: "x" },
    fn: { tag: "Elim", signature: "main__Tag", motive: { tag: "DefRef", name: "main__Around" }, clauses: [loop] } } }, ambient);
  const iShown = "fun (x : Tag(Unit)) => match x as z return Around(z) { tag => loop @ i; }";
  both_(iTerm, iShown);
  // g names no dimension, but is shown where the context names i.
  const gTerm = folded({ tag: "DefRef", name: "main__g" }, ambient);
  const gShown = "fun (x : Tag(Unit)) => match x as z return Around(z) { tag => base; }";
  assert.equal(checker.displayText(gTerm, 1000, 1000, undefined, 256, ambient), gShown);
  assert.equal(checker.displayText(gTerm, 1000, 1000, undefined, 256, new Map()), gShown.replace("Tag(Unit)", "Tag(i)"));
  const { result: back } = await checkProgram(t, `${declarations}def z1_back : fam = fam := path z1 => ${z1Shown};
def i_loop : (fun (x : Tag(Unit)) => match x as z return Around(z) { tag => base; }) = g := path i => ${iShown};
def g_back : g = g := path i => ${gShown};
`, { module });
  assert.deepEqual(back.gaps, []);
});

// forSource on a term of its own, as a test or a tool would name one: an
// eliminator written as a function is spelled out, its argument named apart
// from the dimension x in scope.
test("forSource spells out an eliminator as a function, apart from the dimensions in scope", () => {
  const sort = { tag: "Sort", signature: "main__N", parameters: [], levels: [] };
  const symbols = { main__N: { name: "N", slots: [], constructors: [{ name: "zero", data: 0, positions: 0, dimensions: 0 }] },
    main__p: { name: "p" }, main__T: { name: "T" } };
  const elim = { tag: "Elim", signature: "main__N", motive: { tag: "Lam", name: "m", domain: sort, body: { tag: "DefRef", name: "main__T" } },
    clauses: [{ tag: "PApp", path: { tag: "DefRef", name: "main__p" }, arg: [["x:1"]] }] };
  const definitions = { type: () => null, value: () => null, label: name => symbols[name]?.name ?? name };
  const [named] = forSource([{ tag: "PLam", dim: "x", family: null, body: elim }], { definitions, symbols });
  assert.equal(sourceText(named, symbols), "path x => fun (x1 : N) => match x1 return T { zero => p @ x; }");
  // The printer chooses no name: unnamed, the eliminator shows as it is.
  assert.equal(sourceText({ tag: "PLam", dim: "x", family: null, body: elim }, symbols), "path x => N.elim(λ (m : N). T, at(p, x:1))");
});
