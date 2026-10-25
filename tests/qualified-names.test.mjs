import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { parse, tokenize } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { diagnosticCode } from "../web/diagnostics.mjs";
import { checkProgram } from "./check-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { ContextualSession } from "../web/contextual-session.mjs";
import { verifyMigration } from "../tools/proof-migration.mjs";

// module::name (web/reference/first-proof.html#qualified-names): one of a
// module's declarations, by a name nothing in scope shadows.
const module = await createCubical();
const value = source => { const declaration = parse(source).declarations[0]; return declaration.value ?? declaration.body[0].value; };

test("a qualified name is one token, read where a name refers and refused where one is introduced", () => {
  assert.deepEqual(tokenize("unat::zero").map(token => token.text), ["unat::zero", "EOF"]);
  const name = value("def a := unat::zero;");
  assert.deepEqual([name.kind, name.name, name.moduleQualifier.name], ["name", "unat::zero", "unat"]);
  // A member after it keeps its module.
  assert.equal(value("def a := m::T.Hom;").moduleQualifier.name, "m");
  for (const [source, code] of [["def a := unat :: zero;", "E006"], ["def a := unat:: zero;", "E006"],
    ["def a := (unat)::zero;", "E006"], ["def a := unat::zero::x;", "E005"],
    ["def unat::zero := tt;", "E007"], ["def f := fun (m::x : U0) => m::x;", "E007"], ["def f(m::x : U0) : U0 := Unit;", "E007"]])
    assert.throws(() => parse(source), error => diagnosticCode(error.message) === code, source);
  const source = "import unat;\ndef two : unat::UNat := unat::succ(unat::succ(unat::zero));\n";
  assert.equal(formatCubist(source), source);
});

// The module checked here is main. Each qualified name is the definition,
// though a dimension, a parameter or a local name of its own name is in
// scope; a type and a constructor are named so too.
test("a qualified name names its module's declaration whatever shadows its name", async t => {
  const { result } = await checkProgram(t, `import unat;
use unat;

inductive Circle {
  base;
  loop : base = base;
}

def d0 : base = base := loop;
def under : base = base := path d0 => main::d0 @ d0;
def under_same : under = d0 := refl(d0);
def parameter(d0 : base = base) : base = base := main::d0;
def parameter_same : parameter(refl(base)) = d0 := refl(d0);
def local : base = base {
  let d0 := refl(base);
  exact main::d0;
}
def local_same : local = d0 := refl(d0);
def two : unat::UNat := unat::succ(unat::succ(unat::zero));
evaluate two expecting 2;
`, { module });
  assert.deepEqual(result.gaps, []);
});

test("a qualified name's module is this one or an imported one, and declares the name", async t => {
  // This module's name that it never declares is undeclared, though none
  // of its names is bound yet; its own later name, a constructor's too, is
  // refused as declared below its use, not as unimported or undeclared.
  const { result } = await checkProgram(t, `import unat;

def nowhere := main::nothing;
def own := main::later;
def early := main::point;
def missing := unat::nothing;
def unloaded := hlevels::IsProp;
def later : U0 := Unit;

inductive Tags {
  point;
}
`, { module });
  assert.deepEqual(result.gaps.map(gap => [gap.name, gap.code]),
    [["nowhere", "E254"], ["own", "E255"], ["early", "E255"], ["missing", "E254"], ["unloaded", "E253"]]);
});

// A module the compilation has loaded for another check is not available to
// one that does not import it: the environment, not the compilation's
// record of declarations, says what a name can refer to.
test("a qualified name is available only where its module is imported", async t => {
  const { program, result } = await checkProgram(t, "import hlevels;\ndef here : U1 := hlevels::IsProp(U0, Unit);\n", { module });
  assert.deepEqual(result.gaps, []);
  await program.check("import unat;\ndef elsewhere : U1 := hlevels::IsProp(U0, Unit);\n", "second");
  assert.deepEqual(program.gaps.filter(gap => gap.module === "second").map(gap => [gap.name, gap.code]), [["elsewhere", "E253"]]);
});

// Each reader of a name reads a qualified one as it reads any name: a
// theory's field type, a constructor's call at its expected type, implicit
// and named arguments, an evaluation's pattern, a match's constructors, at
// the top and nested, a rule's name, a hint, a notation's rule, the
// notation namespace, where a selection, an operator's qualifier and use
// name a notation, a theory, its generated names, and a model's field.
const library = sourceReader();
const withModules = sources => (name, importer) => sources[name] ?? library(name, importer);
test("a qualified name is read wherever a name is", async t => {
  const { result } = await checkProgram(t, `import unat;
import hlevels;
use unat;

theory T(U < UU0) {
  M : U;
  point(n : unat::UNat) : M;
  c : M;
}

inductive Box(A : U0) : U0 {
  box(a : A);
}

inductive Opt(A : U0) {
  none;
  some(y : A);
}

def boxed : Box(Unit) := main::box(tt);
def idf{{A : U0}}(a : A) : A := a;
def implicit : Unit := main::idf{{Unit}}(tt);
def named : Unit := main::idf(a := tt);
evaluate succ(zero) expecting unat::succ(_);
def pred(n : UNat) : UNat := match n return UNat { unat::zero => 0; unat::succ(k) => k; };
evaluate pred(3) expecting 2;
def get(o : Opt(UNat)) : UNat := match o return UNat { main::none => 0; main::some(unat::zero) => 1; main::some(unat::succ(k)) => k; };
evaluate get(some(3)) expecting 2;
def two_is : 1 + 1 = 2 := refl(2);
simp_rule main::two_is;
hlevel_rule hlevels::unit_is_prop;
def hinted : 1 + 1 = 2 {
  exact with unfolding [main::two_is] { refl(2) };
}

notation times {
  x + y := unat::mul(x, y);
  numeral(n : UNat) := n;
}

evaluate main::times.(2 + 3) expecting 6;
evaluate unat::unat.(2 + 3) expecting unat::unat.(5);
evaluate 2 unat::unat.(+) 3 expecting 5;
def made : main::T(U0) := main::T.make(Unit, fun (n : UNat) => tt, tt);
def field : Unit := main::made.c;
`, { module });
  assert.deepEqual(result.gaps, []);
  const { result: used } = await checkProgram(t, "import unat;\nuse unat::unat;\ndef two := 2;\n", { module });
  assert.deepEqual(used.gaps, []);
  // Another type's constructor is no constructor of this one.
  const { result: other } = await checkProgram(t, `import unat;
inductive Opt(A : U0) {
  none;
  some(y : A);
}
def wrong(n : UNat) : UNat := match n return UNat { main::none => zero; unat::succ(k) => k; };
`, { module });
  assert.deepEqual(other.gaps.map(gap => [gap.name, gap.code]), [["wrong", "E528"]]);
});

// A module's own notation, where another import takes its label, and a
// notation declared after its model is first used qualified.
test("a qualified name reads its module's own notation", async t => {
  const { result } = await checkProgram(t, "import a;\nimport b;\nevaluate a::n.(tt + tt) expecting tt;\nevaluate b::n.(tt + tt) expecting tt;\n",
    { module, reader: withModules({ a: "notation n {\n  x + y := x;\n}\n", b: "notation n {\n  x + y := y;\n}\n" }) });
  assert.deepEqual(result.gaps, []);
  const { result: later } = await checkProgram(t, `import unat;
use unat;

theory P(U < UU0) {
  M : U;
  pt : M;
}

def m : P(U0) := P.make(UNat, zero);
def saved : P(U0) := main::m;

notation m {
  numeral(n : UNat) := succ(n);
}

evaluate main::m.(0) expecting 1;
`, { module });
  assert.deepEqual(later.gaps, []);
});

// Retained syntax, a theory's, reports a qualified name's refusal; a module
// of notations only is imported, and declares no other name.
test("a qualified name's refusal is reported wherever it is read", async t => {
  const { result } = await checkProgram(t, `theory T2(U < UU0) {
  M : U;
  c(n : missing::Nat) : M;
}

theory T3(U < UU0) {
  M : U;
  c(n : main::Later) : M;
}

def Later : U0 := Unit;
`, { module });
  assert.deepEqual(result.gaps.map(gap => [gap.name, gap.code]), [["T2", "E253"], ["T3", "E255"]]);
  const { result: notations } = await checkProgram(t, "import a;\ndef x : Unit := a::absent;\n",
    { module, reader: withModules({ a: "notation n {\n  x + y := x;\n}\n" }) });
  assert.deepEqual(notations.gaps.map(gap => [gap.name, gap.code]), [["x", "E254"]]);
});

// A contextual console entry reads a qualified name from its scope's
// available declarations, past a parameter of that name.
test("a contextual entry reads a qualified name", async t => {
  const source = "def x : U0 := Unit;\ndef f(x : U1) : U1 {\n  exact x;\n}\n";
  const { program, result } = await checkProgram(t, source, { module, options: { collectScopes: true } });
  assert.deepEqual(result.gaps, []);
  const start = source.indexOf("exact x;");
  const point = [...program.scopePoints.values()].find(point => point.origin.module === "main" && point.origin.start === start && point.phase === "before");
  const session = new ContextualSession(program, point.id);
  t.after(() => session.dispose());
  const run = async input => (await session.run(input))[0];
  assert.equal((await run("typeof x")).text, "U1");
  assert.equal((await run("typeof main::x")).text, "U0");
  const refused = await run("typeof main::y");
  assert.equal(diagnosticCode(refused.text), "E254", refused.text);
});

// The migration verifier checks an edited module as its shadow, whose own
// qualified names name the shadow too.
test("a migration reads a module's qualified names in its shadow", async () => {
  const source = "def x : Unit := tt;\ndef y : Unit := m::x;\n";
  const [report] = await verifyMigration({ modules: ["m"], level: "identical",
    readOriginal: (name, importer) => name === "m" ? source : library(name, importer), readEdited: async () => source });
  assert.deepEqual(report.failures, []);
  assert.equal(report.identical, 2);
});

// Module and declaration names can hold __, so the kernel name a__b__x is
// a's b__x or a__b's x: the declaration's binding names its module.
test("a qualified name names its own module's declaration", async t => {
  const { result } = await checkProgram(t, "import a;\ndef wrong : Unit := a__b::x;\ndef fine : Unit := a::b__x;\n",
    { module, reader: withModules({ a: "def b__x : Unit := tt;\n" }) });
  assert.deepEqual(result.gaps.map(gap => [gap.name, gap.code]), [["wrong", "E253"]]);
});
