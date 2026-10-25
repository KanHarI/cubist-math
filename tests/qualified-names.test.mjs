import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { parse, tokenize } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { diagnosticCode } from "../web/diagnostics.mjs";
import { checkProgram } from "./check-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";

// module::name (web/reference/first-proof.html#qualified-names): one of a
// module's declarations, by a name nothing in scope shadows.
const module = await createCubical();
const value = source => { const declaration = parse(source).declarations[0]; return declaration.value ?? declaration.body[0].value; };

test("a qualified name is a module's name, :: and a name, tight", () => {
  assert.deepEqual(tokenize("unat::zero").map(token => token.text), ["unat", "::", "zero", "EOF"]);
  const name = value("def a := unat::zero;");
  assert.deepEqual([name.kind, name.name, name.moduleQualifier.name], ["name", "unat::zero", "unat"]);
  // A member after it keeps its module.
  assert.equal(value("def a := m::T.Hom;").moduleQualifier.name, "m");
  for (const [source, code] of [["def a := unat :: zero;", "E006"], ["def a := unat:: zero;", "E006"],
    ["def a := (unat)::zero;", "E006"], ["def a := unat::zero::x;", "E005"]])
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
// and named arguments, an evaluation's pattern, a notation's rule, and the
// notation namespace, where a selection and use name a notation.
test("a qualified name is read wherever a name is", async t => {
  const { result } = await checkProgram(t, `import unat;
use unat;

theory T(U < UU0) {
  M : U;
  point(n : unat::UNat) : M;
}

inductive Box(A : U0) : U0 {
  box(a : A);
}

def boxed : Box(Unit) := main::box(tt);
def idf{{A : U0}}(a : A) : A := a;
def implicit : Unit := main::idf{{Unit}}(tt);
def named : Unit := main::idf(a := tt);
evaluate succ(zero) expecting unat::succ(_);

notation times {
  x + y := unat::mul(x, y);
  numeral(n : UNat) := n;
}

evaluate main::times.(2 + 3) expecting 6;
evaluate unat::unat.(2 + 3) expecting unat::unat.(5);
`, { module });
  assert.deepEqual(result.gaps, []);
  const { result: used } = await checkProgram(t, "import unat;\nuse unat::unat;\ndef two := 2;\n", { module });
  assert.deepEqual(used.gaps, []);
});

// Module and declaration names can hold __, so the kernel name a__b__x is
// a's b__x or a__b's x: the declaration's binding names its module.
test("a qualified name names its own module's declaration", async t => {
  const library = sourceReader(), sources = { a: "def b__x : Unit := tt;\n" };
  const { result } = await checkProgram(t, "import a;\ndef wrong : Unit := a__b::x;\ndef fine : Unit := a::b__x;\n",
    { module, reader: (name, importer) => sources[name] ?? library(name, importer) });
  assert.deepEqual(result.gaps.map(gap => [gap.name, gap.code]), [["wrong", "E253"]]);
});
