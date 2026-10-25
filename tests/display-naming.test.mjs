import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { cubicalMathTree, cubicalText } from "../web/cubical-notation.mjs";
import { displayTerm, forSource } from "../web/display-naming.mjs";
import { judgementGraph } from "../web/cubical-graph-view.mjs";
import { sourceText } from "../web/cubical-source-text.mjs";
import { checkProgram } from "./check-program.mjs";
import { localName } from "../web/translator/names.mjs";

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
import hlevels;
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

inductive Two2 {
  two2(p : UNat, q : UNat);
}

inductive Tr(A : U0) : prop {
  point(a : A);
}

inductive LBox(U < UU0) {
  lbox;
}

inductive Box(f : Circle -> Circle) {
  box;
}

inductive Tree {
  leaf;
  node(l : Tree, value : UNat, r : Tree);
}

// Named as the display's binder stems.
def x : U0 := Unit;
def z(s : Unit or Unit) : U0 := Unit;
def k(n : UNat) : U0 := Unit;
def h(n : UNat) : UNat := n;
def a(u : Unit) : Unit := u;
def b(u : Unit) : Unit := u;

// Named as the display's dimension names.
def i(u : Unit) : base = base := path e => loop @ ~e;
def d1 : base = base := path e => loop @ ~e;
def k1(c : Circle) : Circle := match c return Circle { base => base; } obligations by loop;
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
def choose(m, n : UNat) : UNat := m;
def zero_of(u : Unit) : UNat := 0;
def combine(l : Tree, value : UNat, r : Tree, il, ir : UNat) : UNat := value + il + il + ir + ir + ir;
def one_of(u : Unit) : UNat := 1;
def keep2(f : Opt(Unit) -> Unit) : Opt(Unit) -> Unit := f;
def LM(U < UU0, b : LBox(U)) : U0 := Unit;
def BoxM(b : Box(fun (c : Circle) => match c return Circle { base => base; } obligations by loop)) : U0 := Unit;
def dfam : exists A : U0. A -> U0 := (Opt(Unit), Fits);
def stepper(p : UNat, ih : forall k : UNat. (p = p) and (k = k)) : forall k : UNat. (succ(p) = succ(p)) and (k = k) :=
  fun (k : UNat) => (refl(succ(p)), refl(k));
`;

// Each case: a definition's name and its declaration, and inputs at which
// the printed copy must compute what the original does.
const cases = [
  // A clause folded to a definition named as the branch's stem.
  ["sum_clause", "def sum_clause : (Unit or Unit) -> Unit := fun (s : Unit or Unit) => match s return Unit { left u => a(u); right v => b(v); };"],
  // Clauses folded to definitions that tell left from right by computing.
  ["sum_pick", "def sum_pick : (Unit or Unit) -> UNat := fun (s : Unit or Unit) => match s return UNat { left u => zero_of(u); right v => one_of(v); };",
    [["left(tt)", 0], ["right(tt)", 1]]],
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
  // A path clause folded to a definition, applied, named as the
  // dimension's stem; shown where the context names i, i is unfolded, and
  // the path applied reduced.
  ["path_clause", "def path_clause : (Circle -> Circle) and Unit := (fun (c : Circle) => match c return Circle { base => base; loop @ e => i(tt) @ e; }, tt);"],
  // A path clause folded to d1, whose value is ascribed: shown where the
  // context names d1, it unfolds, and the ascription and path reduce.
  ["d1_clause", "def d1_clause : (Circle -> Circle) and Unit := (fun (c : Circle) => match c return Circle { base => base; loop @ e => d1 @ e; }, tt);"],
  // A function named as a dimension whose value has a clause to spell out.
  ["k1_pair", "def k1_pair : (Circle -> Circle) and Unit := (k1, tt);"],
  // A clause folded whole over data and recursive fields: arguments in the
  // constructor's order, then hypotheses, told apart by computing.
  ["tree_sum", "def tree_sum(t : Tree) : UNat := induction t return UNat { leaf => 0; node(l, value, r) with il, ir => combine(l, value, r, il, ir); };",
    [["node(node(leaf, 1, leaf), 2, leaf)", 4], ["node(leaf, 2, node(leaf, 1, leaf))", 5]]],
  // A clause folded whole: two new arguments, told apart by computing.
  ["two2_clause", "def two2_clause : Two2 -> UNat := fun (t : Two2) => match t return UNat { two2(p, q) => choose(p, q); };", [["two2(1, 2)", 1]]],
  // A truncation's squash clause folded past its arguments: hypotheses
  // and a dimension, in that order.
  ["squash_clause", "def squash_clause : Tr(Unit) -> Unit := fun (t : Tr(Unit)) => induction t return Unit { point(a) => a; squash(x, y) @ e with ihx, ihy => unit_is_prop(ihx, ihy) @ e; };"],
  // Induction whose motive binds the name its folded step's predecessor
  // takes: the shared `as` name would capture it.
  ["nat_cap", "def nat_cap(n : UNat) : forall k : UNat. (n = n) and (k = k) := induction n as m return forall k : UNat. (m = m) and (k = k) { zero => fun (k : UNat) => (refl(0), refl(k)); succ ih => stepper(m, ih); };"],
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
  // An eliminator as an application's argument, and one syntax both
  // applied and not.
  ["argued", "def argued : (Opt(Unit) -> Unit) and Unit := (keep2(fun (o : Opt(Unit)) => match o return Unit { none => tt; some(y) => y; }), tt);"],
  ["shared", "def shared : Opt(Unit) -> Unit and (Opt(Unit) -> Unit) := fun (o : Opt(Unit)) => (match o return Unit { none => tt; some(y) => y; }, fun (p : Opt(Unit)) => match p return Unit { none => tt; some(y) => y; });"],
  // Recovered domains that depend on a level and on a pair's first part.
  ["lm", "def lm(b : LBox(U0)) : LM(U0, b) := match b as w return LM(U0, w) { lbox => tt; };"],
  ["lm_refl", "def lm_refl : lm = lm := refl(fun (b : LBox(U0)) => match b as w return LM(U0, w) { lbox => tt; });"],
  ["dm", "def dm(o : dfam.1) : dfam.2(o) := match o as w return dfam.2(w) { none => tt; some(y) => y; };"],
  ["dm_refl", "def dm_refl : dm = dm := refl(fun (o : dfam.1) => match o as w return dfam.2(w) { none => tt; some(y) => y; });"],
  // A recovered domain with an eliminator in it, spelled out in turn.
  ["bm", "def bm(b : Box(fun (c : Circle) => match c return Circle { base => base; } obligations by loop)) : BoxM(b) := match b as w return BoxM(w) { box => tt; };"],
  ["bm_refl", "def bm_refl : bm = bm := refl(fun (b : Box(fun (c : Circle) => match c return Circle { base => base; } obligations by loop)) => match b as w return BoxM(w) { box => tt; });"],
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
  program.kernel.definition(program.kernel.definitions.get(`main__${name}`)).type), [], { width: 1000, limit: 1000 });

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
  for (const dimension of ["i", "j", "d0", "z1", "d1", "k1"]) {
    const context = new Map([[dimension, 0]]);
    for (const [name] of cases) {
      const { expression } = checker.checkSyntax({ tag: "DefRef", name: `main__${name}` }, null, new Map(), context);
      const text = checker.displayText(checker.syntax.decode(kernel.normalizeFolded(expression), context), context, { width: 4000 });
      back.push(`def ${dimension}_${name} : ${name} = ${name} := path ${dimension} => ${text};`);
    }
  }
  const { result } = await checkProgram(t, `${source}${back.join("\n")}\n`, { module });
  assert.deepEqual(result.gaps.map(gap => `${gap.name}: ${gap.code} ${gap.reason}`), []);
});

// No display has a default context: each is given the dimensions of the
// context its terms are shown in, as a scope's Map or their names, [] for
// none (contextDimensions). A view's [name, index] entries are neither.
test("every display is given its context's dimensions", async t => {
  const { program } = await checkProgram(t, "def u : Unit := tt;\n", { module });
  const { checker } = program, term = { tag: "Point" };
  for (const display of [() => checker.displayText(term), () => checker.displayTexts([term]), () => checker.kernelText(term),
    () => checker.displayGoal(new Map(), undefined, term), () => forSource([term], { ...checker.displayNaming([]), dimensions: undefined }),
    () => cubicalText(term), () => checker.displayText(term, [["i", 0]])])
    assert.throws(display, TypeError);
  assert.equal(checker.displayText(term, []), "tt");
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
def op : Opt(Unit) = Opt(Unit) := refl(Opt(Unit));
def famP : PathP(fun (k : Interval) => (op @ k) -> U0, F, F) := path k => F;
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
    assert.equal(checker.displayText(term, [], { width: 1000, limit: 1000 }), shown);
    assert.equal(checker.displayGoal(new Map(), [], term, null, { width: 1000 }).goal, shown);
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
  assert.equal(checker.displayText(gTerm, ambient, { width: 1000, limit: 1000 }), gShown);
  assert.equal(checker.displayText(gTerm, [], { width: 1000, limit: 1000 }), gShown.replace("Tag(Unit)", "Tag(i)"));
  // An eliminator written as a function, its motive a path of type
  // families applied at z1: its domain is the family's at z1.
  const famAt = { tag: "PApp", path: { tag: "DefRef", name: "main__famP" }, arg: [["z1:1"]] };
  const alone = folded({ tag: "Elim", signature: "main__Opt", motive: famAt, clauses }, new Map([["z1", 0]]));
  assert.equal(checker.displayText(alone, [], { width: 1000, limit: 1000 }), "fun (x : op @ z1) => match x as z return (famP @ z1)(z) { none => tt; some(y) => y; }");
  // A goal shown where the context names d0 keeps the name, which reads as
  // an unnamed dimension's; a goal printed in kernel notation, as a
  // judgement graph prints it, is shown as it was checked.
  const loopAt = { tag: "PApp", path: { tag: "Con", index: 1, name: "loop", sort: circle }, arg: [["d0:1"]] };
  assert.equal(checker.displayGoal(new Map(), new Map([["d0", 0]]), loopAt, null, { width: 1000 }).goal, "loop @ d0");
  const kernelGoal = checker.displayGoal(new Map(), [], alone, null, { width: 1000, kernel: true, reduce: false }).goal;
  assert.match(kernelGoal, /^Opt\.elim\(at\(famP, z1:1\), /, kernelGoal);
  // So is one given the judgement's dimensions, as a judgement graph gives
  // them: the definition d0 beside the dimension d0 shows by its kernel name.
  const kVar = { tag: "Var", name: "k" }, kType = { tag: "Pi", name: "_", domain: { tag: "U", level: { tag: "LConst", tier: 0, value: 0 } }, body: { tag: "U", level: { tag: "LConst", tier: 0, value: 0 } } };
  const graphGoal = checker.displayGoal(new Map([["k", kType]]), new Map([["d0", 0]]), { tag: "App", fn: kVar, arg: { tag: "DefRef", name: "main__d0" } }, null,
    { width: 240, kernel: true, reduce: false });
  assert.equal(graphGoal.goal, "k(main__d0)");
  const { result: back } = await checkProgram(t, `${declarations}def z1_back : fam = fam := path z1 => ${z1Shown};
def i_loop : (fun (x : Tag(Unit)) => match x as z return Around(z) { tag => base; }) = g := path i => ${iShown};
def g_back : g = g := path i => ${gShown};
`, { module });
  assert.deepEqual(back.gaps, []);
});

// A judgement graph names its dimensions, as decoding does, d0 and on: the
// definition d0, applied under the dimension d0, shows by its kernel name.
test("a judgement graph keeps a definition apart from the dimensions of its judgements", async t => {
  const { program, result } = await checkProgram(t, `inductive Circle {
  base;
  loop : base = base;
}

def d0 : U0 := Unit;
def at0 : (U0 -> (base = base) -> U0) -> (base = base) -> U0 := fun (k : U0 -> (base = base) -> U0) => k(d0);
def gq : PathP(fun (e : Interval) => (U0 -> (loop @ e = loop @ e) -> U0) -> (loop @ e = loop @ e) -> U0, at0, at0) :=
  path e => fun (k : U0 -> (loop @ e = loop @ e) -> U0) => k(d0);
`, { module });
  assert.deepEqual(result.gaps, []);
  // k's type names the dimension, so k(d0) is a judgement under it, shown
  // as a term of its own that names no dimension.
  const statements = judgementGraph(program, program.inspect("main__gq")).rows.map(row => row.statement).filter(text => /d0 : 𝕀/.test(text) && /k\(/.test(text));
  assert.ok(statements.length, "a judgement under the dimension applies k");
  for (const text of statements) assert.match(text, /k\(main__d0\)/, text);
});

// An entry's fragment, its context and the entry, is shown over the
// fragment's dimensions as a judgement is: a : k(d0, q) under the dimension
// d0 shows the definition d0 by its kernel name.
test("a judgement graph's context fragments keep a definition apart from their dimensions", async t => {
  const { program, result } = await checkProgram(t, `inductive Circle {
  base;
  loop : base = base;
}

def d0 : U0 := Unit;
def at1 : forall k : U0 -> (base = base) -> U0. forall q : base = base. k(d0, q) -> k(d0, q) := fun k => fun q => fun (a : k(d0, q)) => a;
def ga : PathP(fun (e : Interval) => forall k : U0 -> (loop @ e = loop @ e) -> U0. forall q : loop @ e = loop @ e. k(d0, q) -> k(d0, q), at1, at1) :=
  path e => fun k => fun q => fun (a : k(d0, q)) => a;
`, { module });
  assert.deepEqual(result.gaps, []);
  const fragments = judgementGraph(program, program.inspect("main__ga")).entries.map(entry => entry.fragment)
    .filter(fragment => fragment.includes("d0 : 𝕀") && /^a : /.test(fragment.at(-1)));
  assert.ok(fragments.length, "an entry a under the dimension");
  for (const fragment of fragments) assert.equal(fragment.at(-1), "a : k(main__d0, q)", fragment.join(", "));
});

// Induction named by forSource without the elaborator's symbols: spelledOut
// gives the motive's variable and the predecessor one name
// (inductionBinders), the predecessor's first, each binder renamed apart
// from what it would capture, and displayTerm names both alike. Each text
// reads back as the same function. In f, the motive's own binder k is
// renamed apart from the shared k; in g, the successor clause's binder m
// keeps its name; in h, the parameter k is in scope, and the shared name is
// shown apart from it.
const bare = { definitions: { type: () => null, value: () => null, label: localName }, symbols: {}, dimensions: [] };
test("induction's shared name is settled by the naming, without symbols too", async t => {
  const declarations = `import unat;
use unat;

def f(n : UNat) : forall q : n = n. q = q := induction n as m return forall k : m = m. k = k { zero => fun q => refl(q); succ(k) with ih => fun q => refl(q); };
def g(n : UNat) : forall q : n = n. Unit := induction n as m return forall k : m = m. Unit { zero => fun q => tt; succ(k) with ih => fun (m : succ(k) = succ(k)) => tt; };
def h(k : UNat) : forall q : k = k. Unit := induction k as m return forall q : m = m. Unit { zero => fun q => tt; succ(k) with ih => fun q => tt; };
`;
  const { program, result } = await checkProgram(t, declarations, { module });
  assert.deepEqual(result.gaps, []);
  const { kernel, checker } = program;
  for (const [name, spelled, type] of [["f", /induction n as k return forall k1 : k = k\. k1 = k1 /, "n = n. q = q"],
    ["g", /induction n as k return /, "n = n. Unit"], ["h", /induction k as k1 return /, "k = k. Unit"]]) {
    const value = checker.syntax.decode(kernel.definition(kernel.definitions.get(`main__${name}`)).value);
    const shown = sourceText(forSource([value], bare)[0], {}, 4000, { selection: "unat" });
    assert.match(shown, spelled, shown);
    const { result: back } = await checkProgram(t, `${declarations}def back : forall ${name === "h" ? "k" : "n"} : UNat. forall q : ${type} := ${shown};
def same : back = ${name} := refl(${name});
`, { module });
    assert.deepEqual(back.gaps, [], shown);
  }
});

// The successor clause binds k again, over a type whose binder m has the
// predecessor k in its scope, or binds a dimension k: the shared name is
// apart from both, and the clause's own binders from it. Where the motive
// shows k for another variable, the motive's name m is shared, and where
// the successor clause shows m for another one too, a new name. The
// printer, on terms not named, shows the motive's variable and the
// predecessor as they are, unalike: kernel notation.
test("induction's shared name captures nothing in its successor clause", () => {
  const nat = { tag: "Sort", signature: "unat__UNat", parameters: [], levels: [] };
  const v = name => ({ tag: "Var", name }), app = (fn, ...args) => args.reduce((fn, arg) => ({ tag: "App", fn, arg }), fn);
  const motive = { tag: "Lam", name: "m", domain: nat, body: { tag: "Pi", name: "k", domain: app(v("T"), v("m")), body: app(v("T"), v("m")) } };
  const induction = body => ({ tag: "App", arg: v("n"), fn: { tag: "Elim", signature: "unat__UNat", motive, clauses: [v("z"),
    { tag: "Lam", name: "k", domain: nat, body: { tag: "Lam", name: "ih", domain: v("I"), body } }] } });
  const named = term => sourceText(forSource([term], bare)[0], {}, 4000, { selection: "unat" });
  const rebinding = { tag: "Lam", name: "k", domain: { tag: "Pi", name: "m", domain: nat, body: app(v("R"), v("m"), v("k")) }, body: { tag: "Point" } };
  assert.equal(named(induction(rebinding)),
    "induction n as k return T(k) -> T(k) { zero => z; succ ih => fun (k1 : forall m : UNat. R(m, k)) => tt; }");
  assert.equal(named(induction({ tag: "PLam", dim: "k", family: null, body: { tag: "PApp", path: app(v("R"), v("k")), arg: [["k:1"]] } })),
    "induction n as k1 return T(k1) -> T(k1) { zero => z; succ ih => path k => R(k1) @ k; }");
  const outer = { tag: "Lam", name: "m", domain: nat, body: app(v("T"), v("k")) };
  assert.equal(named({ tag: "App", arg: v("n"), fn: { tag: "Elim", signature: "unat__UNat", motive: outer, clauses: [v("z"),
    { tag: "Lam", name: "k", domain: nat, body: { tag: "Lam", name: "ih", domain: v("I"), body: app(v("S"), v("k")) } }] } }),
    "induction n as m return T(k) { zero => z; succ ih => S(m); }");
  // The successor clause shows m for another variable too: a new name.
  assert.equal(named({ tag: "App", arg: v("n"), fn: { tag: "Elim", signature: "unat__UNat", motive: outer, clauses: [v("z"),
    { tag: "Lam", name: "k", domain: nat, body: { tag: "Lam", name: "ih", domain: v("I"), body: app(v("S"), v("k"), v("m")) } }] } }),
    "induction n as k1 return T(k) { zero => z; succ ih => S(k1, m); }");
  // A new name is numbered apart from the universes: U_1, not U1, though a
  // term too large for scoped names (globalNames) shows it as it is.
  const universal = { tag: "App", arg: v("n"), fn: { tag: "Elim", signature: "unat__UNat", motive: { tag: "Lam", name: "m", domain: nat, body: app(v("Ty"), v("U")) },
    clauses: [v("z"), { tag: "Lam", name: "U", domain: nat, body: { tag: "Lam", name: "ih", domain: v("I"), body: app(v("S"), v("U"), v("m")) } }] } };
  let large = v("w");
  for (let level = 0; level < 11; level++) large = { tag: "Pair", first: large, second: large };
  assert.equal(sourceText(forSource([universal, large], bare)[0], {}, 4000, { selection: "unat" }),
    "induction n as U_1 return Ty(U) { zero => z; succ ih => S(U_1, m); }");
  assert.equal(sourceText(induction(rebinding), {}, 4000, { selection: "unat" }),
    "unat__UNat.elim(λ (m : unat__UNat). (T(m) → T(m)), z, λ (k : unat__UNat). λ (ih : I). λ (k : Π (m : unat__UNat), R(m, k)). ⋆)(n)");
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
  const [named] = forSource([{ tag: "PLam", dim: "x", family: null, body: elim }], { definitions, symbols, dimensions: [] });
  assert.equal(sourceText(named, symbols), "path x => fun (x1 : N) => match x1 return T { zero => p @ x; }");
  // The printer chooses no name: unnamed, the eliminator shows as it is.
  assert.equal(sourceText({ tag: "PLam", dim: "x", family: null, body: elim }, symbols), "path x => N.elim(λ (m : N). T, at(p, x:1))");
  // One eliminator, applied first and then alone: each place is spelled for
  // itself, though the syntax is shared.
  const shared = { tag: "Lam", name: "o", domain: sort, body: { tag: "Pair", first: { tag: "App", fn: elim, arg: { tag: "Var", name: "o" } }, second: elim } };
  const [both] = forSource([shared], { definitions, symbols, dimensions: [] });
  assert.equal(sourceText(both, symbols), "fun (o : N) => (match o return T { zero => p @ x; }, fun (x1 : N) => match x1 return T { zero => p @ x; })");
  // A motive that reduces to a function gives its domain: here of a type
  // with a parameter, whose domain only the function tells.
  const typed = { ...symbols, main__P: { name: "P", slots: ["parameter"], constructors: [{ name: "pz", data: 0, positions: 0, dimensions: 0 }] } };
  const pUnit = { tag: "Sort", signature: "main__P", parameters: [{ tag: "Unit" }], levels: [] };
  const redex = { tag: "App", fn: { tag: "Lam", name: "u", domain: { tag: "Unit" }, body: { tag: "Lam", name: "m", domain: pUnit, body: { tag: "DefRef", name: "main__T" } } }, arg: { tag: "Point" } };
  const [reduced] = forSource([{ tag: "Elim", signature: "main__P", motive: redex, clauses: [{ tag: "Point" }] }], { definitions, symbols: typed, dimensions: [] });
  assert.equal(sourceText(reduced, typed), "fun (x : P(Unit)) => match x return T { pz => tt; }");
  // Terms shown together get new names apart from all of them: the source
  // Nat eliminators of a large tuple take n, n1, …, none n5, which the other
  // term's variable is, and shows as n.
  const nat = { tag: "Sort", signature: "unat__UNat", parameters: [], levels: [] };
  let tuple = Array.from({ length: 256 }, (_, k) => ({ tag: "Elim", signature: "unat__UNat",
    motive: { tag: "Lam", name: "m", domain: nat, body: { tag: "Var", name: `T${k}` } }, clauses: [{ tag: "Var", name: `z${k}` }, { tag: "Var", name: `s${k}` }] }));
  while (tuple.length > 1) tuple = Array.from({ length: Math.ceil(tuple.length / 2) }, (_, k) => ({ tag: "Pair", first: tuple[2 * k], second: tuple[2 * k + 1] ?? tuple[2 * k] }));
  const [, alone] = forSource([tuple[0], { tag: "Var", name: "n5" }], { definitions, symbols, names: new Map([["n5", "n"]]), dimensions: [] });
  assert.equal(sourceText(alone, symbols), "n");
  // A definition named as a dimension of the context, q, applied: its value,
  // a function of a path, leaves a redex at each level of the spine above
  // it, each reduced: q(tt) @ j is p @ ~j.
  const unfolding = { ...definitions, value: name => name === "main__q" ? { tag: "Lam", name: "u", domain: { tag: "Unit" },
    body: { tag: "PLam", dim: "e", family: null, body: { tag: "PApp", path: { tag: "DefRef", name: "main__p" }, arg: [["e:0"]] } } } : null,
    label: name => name === "main__q" ? "q" : definitions.label(name) };
  const applied = { tag: "PApp", path: { tag: "App", fn: { tag: "DefRef", name: "main__q" }, arg: { tag: "Point" } }, arg: [["j:1"]] };
  const [spelled] = forSource([applied], { definitions: unfolding, symbols, dimensions: ["q", "j"] });
  assert.equal(sourceText(spelled, symbols), "p @ ~j");
  // As the kernel keeps such a value, its path ascribed: the spine consumes
  // the value, its ascription first.
  const ascribed = { ...unfolding, value: name => name === "main__q" ? { tag: "Lam", name: "u", domain: { tag: "Unit" },
    body: { tag: "App", fn: { tag: "Lam", name: "ascription", domain: { tag: "Var", name: "A" }, body: { tag: "Var", name: "ascription" } },
      arg: { tag: "PLam", dim: "e", family: { tag: "Var", name: "A" }, body: { tag: "PApp", path: { tag: "DefRef", name: "main__p" }, arg: [["e:0"]] } } } } : null };
  const [consumed] = forSource([applied], { definitions: ascribed, symbols, dimensions: ["q", "j"] });
  assert.equal(sourceText(consumed, symbols), "p @ ~j");
  // Its value applies its argument, a path: the contraction puts the path
  // at a spine's root, a redex the unfolding made, contracted in turn. The
  // term's own redex, the identity applied to that path, is kept.
  const pathArgument = { tag: "PLam", dim: "e", family: { tag: "Var", name: "A" }, body: { tag: "PApp", path: { tag: "DefRef", name: "main__p" }, arg: [["e:1"]] } };
  const applying = { ...definitions, value: name => name === "main__q" ? { tag: "Lam", name: "r", domain: { tag: "Var", name: "A" },
    body: { tag: "PLam", dim: "f", family: { tag: "Var", name: "A" }, body: { tag: "PApp", path: { tag: "Var", name: "r" }, arg: [["f:0"]] } } } : null,
    label: name => name === "main__q" ? "q" : definitions.label(name) };
  const identity = { tag: "Lam", name: "y", domain: { tag: "Unit" }, body: { tag: "Var", name: "y" } };
  const [pathApplied] = forSource([{ tag: "Pair", first: { tag: "App", fn: { tag: "DefRef", name: "main__q" }, arg: pathArgument },
    second: { tag: "App", fn: identity, arg: pathArgument } }], { definitions: applying, symbols, dimensions: ["q"], reduce: 0 });
  assert.equal(sourceText(pathApplied, symbols), "(path f => p @ ~f, (fun (y : Unit) => y)(path e => p @ e))");
  // An eta-reduced clause that is such a definition, its value a redex of
  // its own: the clause takes the path its head reduces to, spelled out
  // again, so that the path the contraction put at a spine's root is
  // contracted too.
  const looped = { ...symbols, main__S: { name: "S", slots: [], constructors: [{ name: "loop", data: 0, positions: 0, dimensions: 1 }] } };
  const redexValue = { ...definitions, value: name => name === "main__q" ? { tag: "App", fn: applying.value("main__q"), arg: pathArgument } : null,
    label: applying.label };
  const loopElim = { tag: "Elim", signature: "main__S", motive: { tag: "Lam", name: "x", domain: { tag: "Sort", signature: "main__S", parameters: [], levels: [] },
    body: { tag: "DefRef", name: "main__T" } }, clauses: [{ tag: "DefRef", name: "main__q" }] };
  const [settled] = forSource([loopElim], { definitions: redexValue, symbols: looped, dimensions: ["q"] });
  assert.equal(sourceText(settled, looped), "fun (x : S) => match x return T { loop @ f => p @ ~f; }");
});

// A definition named as the context's dimension q is unfolded, and every
// redex its value makes contracted, however it is reached: through an
// ascribed argument the value applies, through a value that is a function
// applied twice, through the display's beta reduction, and through an
// eta-reduced clause or its part below a binder. Each text reads back as
// the value. A redex the
// term has of its own, though it shares the very syntax of the value, is
// kept.
test("an unfolding contracts every redex it makes, and only those", async t => {
  const circle = `inductive Circle {
  base;
  loop : base = base;
}
`;
  // Each program is checked in a subtest of its own, which disposes of it:
  // a module holds eight kernel sessions.
  const values = [
    "def q(r : base = base) : base = base := path f => r @ ~f;\ndef g : base = base := q(typed(base = base, path e => loop @ e));",
    "def q : base = base := (fun (u : Unit) => fun (r : base = base) => r)(tt, path e => loop @ e);\ndef g : base = base := path j => q @ ~j;",
    // The display's own beta reduction contracts the redexes it makes, of
    // an unfolded value's and of the term's own: here a path put at a path
    // application's root.
    "def q(r : base = base) : base = base := path f => r @ ~f;\ndef g : base = base := path k => (fun (p : base = base) => q(p))(path j => loop @ j) @ k;",
    "def g : base = base := path k => (fun (p : base = base) => typed(base = base, path f => p @ ~f))(path j => loop @ j) @ k;"];
  for (const [index, definitions] of values.entries()) await t.test(`value ${index + 1}`, async t => {
    const { program, result } = await checkProgram(t, `${circle}${definitions}\n`, { module });
    assert.deepEqual(result.gaps, []);
    const { kernel, checker } = program;
    const text = checker.displayText(checker.syntax.decode(kernel.definition(kernel.definitions.get("main__g")).value), ["q"], { width: 4000 });
    assert.doesNotMatch(text, /\bq\b/, text);
    const { result: back } = await checkProgram(t, `${circle}${definitions}\ndef back : g = g := path q => ${text};\n`, { module });
    assert.deepEqual(back.gaps, [], text);
  });
  // A folded normal form keeps an eta-reduced clause that is the
  // definition, a function of the clause's argument to a path, or a clause
  // whose part below its own binder is: settled at each binder the clause
  // takes, with no beta reduction for display too, as evaluation prints.
  for (const edge of ["q(u) @ j", "q(tt) @ j"]) await t.test(`clause ${edge}`, async t => {
    const edges = `${circle}inductive S {
  pt;
  edge(u : Unit) : pt = pt;
}
def q(u : Unit) : base = base := path e => loop @ ~e;
def g : S -> Circle := fun (s : S) => match s return Circle { pt => base; edge(u) @ j => ${edge}; };
`;
    const { program, result } = await checkProgram(t, edges, { module });
    assert.deepEqual(result.gaps, []);
    const { kernel, checker } = program, context = new Map([["q", 0]]);
    const { expression } = checker.checkSyntax({ tag: "DefRef", name: "main__g" }, null, new Map(), context);
    for (const reduce of [0, 256]) {
      const text = checker.displayText(checker.syntax.decode(kernel.normalizeFolded(expression), context), context, { width: 4000, reduce });
      assert.match(text, /edge\(u\) @ (\w+) => loop @ ~\1;/, text);
      const { result: back } = await checkProgram(t, `${edges}def back : g = g := path q => ${text};\n`, { module });
      assert.deepEqual(back.gaps, [], text);
    }
  });
  // A projection contracted selects its own component, through the
  // display's beta reduction and through an unfolding, of a pair whose
  // components differ.
  const pairs = [
    ["Unit", "def g : U0 := (fun (p : U0 and Unit) => p.1)((Unit, tt));"],
    ["tt", "def g : Unit := (fun (p : U0 and Unit) => p.2)((Unit, tt));"],
    ["Unit", "def q : U0 and Unit := (Unit, tt);\ndef g : U0 := q.1;"],
    ["tt", "def q : U0 and Unit := (Unit, tt);\ndef g : Unit := q.2;"]];
  for (const [index, [component, definitions]] of pairs.entries()) await t.test(`pair ${index + 1}`, async t => {
    const { program, result } = await checkProgram(t, `${definitions}\n`, { module });
    assert.deepEqual(result.gaps, []);
    const { kernel, checker } = program;
    assert.equal(checker.displayText(checker.syntax.decode(kernel.definition(kernel.definitions.get("main__g")).value), ["q"]), component);
  });
  await t.test("shared syntax", async t => {
    const { program } = await checkProgram(t, "def q(u : Unit) : Unit := u;\n", { module });
    const { kernel, checker } = program, value = checker.syntax.decode(kernel.definition(kernel.definitions.get("main__q")).value);
    const pair = { tag: "Pair", first: { tag: "DefRef", name: "main__q" }, second: { tag: "App", fn: value, arg: { tag: "Point" } } };
    assert.equal(checker.displayText(pair, ["q"], { width: 4000, reduce: 0 }),
      "(fun (u : Unit) => (fun (ascription : Unit) => ascription)(u), (fun (u : Unit) => (fun (ascription : Unit) => ascription)(u))(tt))");
  });
});

// An ascription is the term's own redex, kept though the eliminator in its
// type is spelled out: evaluation's weak head leaves one inside the value.
test("a display keeps the term's own redexes", async t => {
  const declarations = `inductive N { zero; }
inductive C { base; loop : base = base; }
def P : U0 := typed((match zero return C { zero => base; }) = base, path i => loop @ i) = loop;
print(evaluate(!P));
`;
  const { result } = await checkProgram(t, declarations, { module });
  const text = result.prints[0].text;
  assert.match(text, /=> ascription\)\(path i => loop @ i\) = loop$/, text);
  const { result: back } = await checkProgram(t, `${declarations}def back : U0 := ${text};\ndef same : back = P := refl(P);\n`, { module });
  assert.deepEqual(back.gaps, [], text);
});
