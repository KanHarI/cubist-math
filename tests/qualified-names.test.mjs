import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { parse, tokenize } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { diagnosticCode } from "../web/diagnostics.mjs";
import { checkProgram } from "./check-program.mjs";

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
  // of its names is bound yet; its own later name is refused as declared
  // below its use, not as unimported or undeclared.
  const { result } = await checkProgram(t, `import unat;

def nowhere := main::nothing;
def own := main::later;
def missing := unat::nothing;
def unloaded := hlevels::IsProp;
def later : U0 := Unit;
`, { module });
  assert.deepEqual(result.gaps.map(gap => [gap.name, gap.code]), [["nowhere", "E254"], ["own", "E255"], ["missing", "E254"], ["unloaded", "E253"]]);
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
