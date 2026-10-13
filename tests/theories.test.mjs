// Theories (L2.4): what the verdicts and prints of cubist-tests/theories.cubist
// and theory_morphisms.cubist do not show. A theory is checked as the declarations it expands to, each
// inspectable by name and assumption-free; its syntax parses and formats
// stably; and its own refusals of form are the parser's.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { parse } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { currentSyntax, historicalSource } from "../web/cubist/legacy-syntax.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { checkProgram, testModule } from "./check-program.mjs";

const module = await createCubical();
const theories = testModule("theories", { module });

test("theory constructors keep header parameters apart from generated field binders", async () => {
  const { get } = await testModule("theory_headers")();
  for (const name of ["named_nat", "named_hom", "named_iso", "named_by_fields"])
    assert.equal(get(name).verified, true, name);
});

test("a theory checks as its model type, constructor, projections, parents' models, homomorphisms and isomorphisms", async () => {
  const { program } = await theories();
  const generated = Object.values(program.symbols)
    .filter(info => info.binding === "theories__Group" || info.binding.startsWith("theories__Group.")).map(info => info.name);
  assert.deepEqual(generated, ["Group", "Group.make", "Group.M", "Group.M_is_set", "Group.mul", "Group.mul_assoc",
    "Group.one", "Group.one_mul", "Group.mul_one", "Group.inv", "Group.inv_mul", "Group.monoid",
    // Its homomorphisms: a map preserving mul, one and inv; and isomorphisms.
    "Group.Hom", "Group.Hom.make", "Group.Hom.map", "Group.Hom.map_mul", "Group.Hom.map_one", "Group.Hom.map_inv",
    "Group.Hom.id", "Group.Hom.compose", "Group.Hom.monoid",
    "Group.Iso", "Group.Iso.make", "Group.Iso.to", "Group.Iso.from", "Group.Iso.from_to", "Group.Iso.to_from",
    "Group.Iso.id", "Group.Iso.compose", "Group.Iso.inverse"]);
  for (const name of generated) {
    const info = program.symbols[`theories__${name}`];
    assert.equal(info.verified, true, name);
    assert.deepEqual(info.axioms, [], name);
  }
  // Two copies of Monoid on one sort: the renamed fields, the shared sort
  // and its evidence once.
  const semiring = Object.values(program.symbols)
    .filter(info => info.binding === "theories__Semiring" || info.binding.startsWith("theories__Semiring.")).map(info => info.name);
  assert.deepEqual(semiring.slice(0, 12), ["Semiring", "Semiring.make", "Semiring.R", "Semiring.R_is_set",
    "Semiring.add", "Semiring.add_assoc", "Semiring.zero", "Semiring.zero_add", "Semiring.add_zero", "Semiring.add_comm",
    "Semiring.mul", "Semiring.mul_assoc"]);
  assert.ok(semiring.includes("Semiring.additive_") && semiring.includes("Semiring.multiplicative"));
});

// Here rather than in theory_morphisms.cubist: the linter (W706) would have
// pair written M -> M -> M, whose carrier on both sides of an arrow has no
// homomorphisms.
test("an operation whose arguments share one domain has homomorphisms, preserving it and computing", async t => {
  const { result } = await checkProgram(t, `import nat;
import hlevels;
use nat;

theory Pair(U < UU0) {
  M : set U;
  pair : forall x, y : M. M;
}

def nat_pair : Pair(U0) := Pair.make(Nat, nat_is_set, add);

def preserved(A, B : Pair(U0), f : Pair.Hom(A, B), x, y : A.M) :
  f.map(A.pair(x, y)) = B.pair(f.map(x), f.map(y)) := f.map_pair(x, y);

def composite : Pair.Hom.compose(Pair.Hom.id(nat_pair), Pair.Hom.id(nat_pair)).map(5) = 5 {
  rfl;
}
`, { module, name: "grouped" });
  assert.deepEqual(result.gaps, []);
  assert.equal(result.complete, true);
});

// A group that repeats a name still takes an argument for each occurrence;
// the body reads the last.
test("an operation whose group repeats a name has homomorphisms for each argument", async t => {
  const { result } = await checkProgram(t, `import nat;
import hlevels;
use nat;

theory T(U < UU0) {
  M : set U;
  op : forall x, x : M. M;
}

def second : T(U0) := T.make(Nat, nat_is_set, fun x => fun y => y);

def preserved(A, B : T(U0), f : T.Hom(A, B), x, y : A.M) :
  f.map(A.op(x, y)) = B.op(f.map(x), f.map(y)) := f.map_op(x, y);

def composite : T.Hom.compose(T.Hom.id(second), T.Hom.id(second)).map(second.op(3, 5)) = 5 {
  rfl;
}
`, { module, name: "repeated" });
  assert.deepEqual(result.gaps, []);
  assert.equal(result.complete, true);
});

test("fresh operation binders avoid theory parameters absent from the field type", async t => {
  const { result } = await checkProgram(t, `import hlevels;
theory T(U < UU0, M_1 : Unit) {
  M : set U;
  op(M : M) : Unit;
}
def preserved(A, B : T(U0, tt), f : T.Hom(A, B), x : A.M) :
  A.op(x) = B.op(f.map(x)) := f.map_op(x);
def composite(S : T(U0, tt), x : S.M) :
  T.Hom.compose(T.Hom.id(S), T.Hom.id(S)).map(x) = x { rfl; }
def iso_composite(S : T(U0, tt), x : S.M) :
  T.Iso.compose(T.Iso.id(S), T.Iso.id(S)).to.map(x) = x { rfl; }
`, { module, name: "fresh_parameters" });
  assert.deepEqual(result.gaps, []);
  assert.equal(result.complete, true);
});

test("theory syntax parses with its parents, renamings and notations, and formats stably", () => {
  const source = `import hlevels;

theory Monoid(U < UU0) {
  M : set U;
  mul(x, y : M) : M notation x * y;
  one : M;
  law one_mul(x : M) : one * x = x;
}

theory Rig(U < UU0) extends additive_ : Monoid(
  M := R, mul := add notation x + y, one := zero, one_mul := zero_add
), Monoid(M := R) {
  law mul_add(x, y, z : R) : x * (y + z) = x * y + x * z;
}
`;
  const [monoid, rig] = parse(source).declarations;
  assert.equal(monoid.kind, "theory");
  assert.deepEqual(monoid.fields.map(field => [field.kind, field.name.text]),
    [["sort", "M"], ["operation", "mul"], ["operation", "one"], ["law", "one_mul"]]);
  assert.equal(monoid.fields[1].notation.operator, "*");
  assert.deepEqual(rig.parents.map(parent => [parent.label?.text ?? null, parent.name.text,
    parent.renaming.map(r => `${r.from.text}:=${r.to.text}${r.notation ? ` ${r.notation.operator}` : ""}`)]),
  [["additive_", "Monoid", ["M:=R", "mul:=add +", "one:=zero", "one_mul:=zero_add"]], [null, "Monoid", ["M:=R"]]]);
  assert.equal(formatCubist(source), source);
  assert.deepEqual(monoid.universes.map(u => u.text), ["U"]);
  assert.deepEqual([monoid.fields[0].level, monoid.fields[0].universe.text], ["set", "U"]);
  const squeezed = "import hlevels;\ntheory Magma(U<UU0) { M : set U; mul(x, y : M) : M notation x * y;\n law idem(x : M) : x * x = x; }\n";
  const formatted = formatCubist(squeezed);
  assert.equal(formatted, "import hlevels;\ntheory Magma(U < UU0) {\n  M : set U;\n  mul(x, y : M) : M notation x * y;\n  law idem(x : M) : x * x = x;\n}\n");
  assert.equal(formatCubist(formatted), formatted);
  // Each dot of a longer qualified name stays tight.
  const nested = "def forget(G : CommGroup(U0)) : Monoid(U0) := G.comm_monoid.monoid;\n";
  assert.equal(formatCubist(nested), nested);
});

test("a carrier is a set, a proposition or a bare type in the header's universe, which the header names", () => {
  const fields = body => parse(`theory T(U < UU0) {\n${body}\n}`).declarations[0].fields
    .map(field => [field.kind, field.name.text, field.level ?? null]);
  assert.deepEqual(fields("M : set U; P : prop U; L : U; one : M;"),
    [["sort", "M", "set"], ["sort", "P", "prop"], ["sort", "L", null], ["operation", "one", null]]);
  // A carrier may have another name; set and prop cannot name fields.
  assert.deepEqual(fields("set_ : U; M : set U; point : set_;"), [["sort", "set_", null], ["sort", "M", "set"], ["operation", "point", null]]);
  assert.throws(() => parse("theory T(U < UU0) { M : set V; }"),
    /V is not the universe of T's carriers: name it in the header, as in theory T\(V < UU0\)\./);
  assert.throws(() => parse("theory T { M : set U; }"), /U is not the universe of T's carriers/);
  assert.throws(() => parse("theory T(U < U1) { }"), /A theory's universes are below UU0: U < UU0\./);
});

test("a theory's header binds several universes and parameters, in order", () => {
  const [module, pair] = parse("theory Module(U < UU0, R : CommRing(U)) { V : set U; }\ntheory Pair(U, V < UU0) { A : set U; B : set V; }")
    .declarations;
  assert.deepEqual([module.universes.map(u => u.text), module.params.map(p => p.name.text)], [["U"], ["R"]]);
  assert.deepEqual([pair.universes.map(u => u.text), pair.fields.map(f => f.universe.text)], [["U", "V"], ["U", "V"]]);
  const source = "theory Module(U < UU0, R : CommRing(U)) {\n  V : set U;\n}\n";
  assert.equal(formatCubist(source), source);
});

test("sort, a carrier's spelling until L2.4c, is refused with the field that replaces it", () => {
  assert.throws(() => parse("theory T { sort M : set; }"),
    /A carrier is a field: write M : set U; or M : prop U;, with the universe named in the header, theory T\(U < UU0\)\./);
  // Renamed fields keep their role.
  assert.deepEqual(parse("theory T(U < UU0) { sort_ : U; }").declarations[0].fields.map(f => f.name.text), ["sort_"]);
});

test("the parser refuses a theory's malformed fields", () => {
  const refused = (body, message) => assert.throws(() => parse(`theory T(U < UU0) {\n${body}\n}`), message);
  refused("M : set U; mul(x, y : M) : M notation x ++ y;", /A notation binds an operator: x \+ y, x - y, x \* y, x \/ y, x \^ y, x < y, x <= y, or -x\./);
  refused("M : set U; gt(x, y : M) : U notation x > y;", /x > y is y < x: a notation binds < and <=, and > and >= follow them\./);
  refused("M : set U; one M;", /Expected ':' and the type of one, as in mul\(x, y : M\) : M;/);
  refused("M : set U; law unit(x : M) x = x;", /Expected ':' and the type of unit, as in law mul_one\(x : M\) : x \* one = x;/);
  assert.throws(() => parse("theory T(U < UU0) {\n  M : set U;\n"), /Expected '}' to close the theory\./);
  // Previously contextual field names have been migrated.
  assert.equal(parse("theory T { law_ : Unit; sort_ : Unit; }").declarations[0].fields.map(f => f.name.text).join(), "law_,sort_");
});

test("a section is parsed and formatted as one item, and refused in its form", () => {
  const source = "section {{U < UU0}}(n : U) { def a := n; def b(m : Nat) : Nat := m;\n}\ndef c := 0;\n";
  const [a, b, c] = parse(source).declarations;
  assert.deepEqual([a.section.declared, b.section.declared, c.section], [[], ["a"], undefined]);
  assert.deepEqual(b.section.params.map(p => [p.name.text, !!p.implicit]), [["U", true], ["n", false]]);
  const formatted = formatCubist(source);
  assert.equal(formatted, "section {{U < UU0}}(n : U) {\n  def a := n;\n\n  def b(m : Nat) : Nat := m;\n}\n\ndef c := 0;\n");
  assert.equal(formatCubist(formatted), formatted);
  assert.throws(() => parse("section (n : Nat) { section (m : Nat) { } }"), /Sections do not nest: close this one with \} first\./);
  assert.throws(() => parse("section { def a := 0; }"), /A section gives its definitions parameters/);
  assert.throws(() => parse("section (n : Nat) { def a := n;"), /Expected '}' to close the section\./);
  assert.throws(() => parse("section (n : Nat) { inductive T { t; } }"), /A section holds definitions: def and computable def\./);
  // An ordinary parameter uses a different name.
  assert.equal(parse("def f(section_ : Nat) := section_;").declarations[0].name.text, "f");
});

test("a theory declared in one module is read, opened and printed in another", async t => {
  const modules = {
    structures: `import hlevels;

theory Magma(U < UU0) {
  M : set U;
  mul(x, y : M) : M notation x * y;
}
`,
    uses: `import structures;

def square(G : Magma(U0), x : G.M) : G.M {
  use G;
  exact x * x;
}

def twice(G : Magma(U0), x : G.M) : G.M := G.mul(x, x);

def same(G : Magma(U0), x : G.M) : square(G, x) = twice(G, x) {
  rfl;
}

def idempotent(G : Magma(U0), x : G.M) : G.mul(x, x) = x {
  rfl;
}
`,
  };
  const library = sourceReader();
  const readSource = async (name, importer) => modules[name] ?? library(name, importer);
  const program = new CubicalProgram(await createCubical(), readSource);
  t.after(() => program.dispose());
  const result = await program.check(modules.uses, "uses");
  // Only the false claim is refused, and its message shows the field as G.mul.
  assert.deepEqual(result.gaps.map(gap => gap.name), ["idempotent"]);
  assert.match(result.gaps[0].reason, /expected G\.mul\(x, x\) = x/);
});

test("open, use's earlier spelling, is refused with a message naming use", () => {
  assert.throws(() => parse("def f(G : M) : Nat { open G; exact 0; }"), /open is now use: write use m; to select a model's fields and notation\./);
  assert.equal(currentSyntax("def f(G : M) : Nat {\n  open G;\n  exact 0;\n}\n"), "def f(G : M) : Nat {\n  use G;\n  exact 0;\n}\n");
});

test("a source from before L2.4c is read with carriers, a header and T for T.Model", () => {
  const old = "theory Monoid extends Semigroup {\n  sort M : set;\n  sort P : prop;\n}\ndef f(G : Monoid.Model(U0), sort : Nat) : G.M := G.one;\n";
  assert.equal(historicalSource(old, "old", { implicitNat: false, minusReverses: false }),
    "theory Monoid(U < UU0) extends Semigroup {\n  M : set U;\n  P : prop U;\n}\ndef f(G : Monoid(U0), sort_ : Nat) : G.M := G.one;\n");
  assert.doesNotThrow(() => parse(historicalSource(old, "old", { implicitNat: false, minusReverses: false })));
});

test("arithmetic groups as L2.10b says, with the cubical operators tightest", () => {
  const show = n => n.kind === "binary" || n.kind === "pathApply" ? `(${show(n.left)} ${n.operator} ${show(n.right)})`
    : n.kind === "negation" ? `(-${show(n.operand)})` : n.kind === "unary" ? `(~${show(n.operand)})` : n.name ?? String(n.value);
  const grouping = source => show(parse(source, true));
  assert.equal(grouping("-x^2"), "(-(x ^ 2))");
  assert.equal(grouping("-x * y"), "((-x) * y)");
  assert.equal(grouping("-p @ i"), "(-(p @ i))");
  assert.equal(grouping("p @ i^2"), "((p @ i) ^ 2)");
  assert.equal(grouping("x * p @ i"), "(x * (p @ i))");
  assert.equal(grouping("a - b - c"), "((a - b) - c)");
  assert.equal(grouping("a / b * c"), "((a / b) * c)");
  assert.equal(grouping("x ^ y ^ z"), "(x ^ (y ^ z))");
  assert.equal(grouping("x >= y + 1"), "(x >= (y + 1))");
  assert.equal(grouping("~p @ i"), "((~p) @ i)");
  // A qualified negation after a space; a qualified operation called.
  assert.equal(parse("G.(-) x", true).kind, "negation");
  assert.equal(parse("G.(-)(x, y)", true).kind, "call");
  for (const source of ["x - y;", "a / b;", "x ^ 2;", "x >= y;"]) {
    const formatted = formatCubist(`def f := ${source}\n`);
    assert.equal(formatCubist(formatted), formatted);
  }
});

test("a refused use belongs to its theory and children report that failed dependency", async t => {
  const source = `import hlevels;
use Nat;
theory T(U < UU0) { M : set U; c : M; }
theory C extends T {}
initial N : T(U0);`;
  const { result } = await checkProgram(t, source, { module });
  const failures = result.outputs.filter(o => !o.verified);
  assert.deepEqual(failures.map(o => [o.name, o.code]), [["T", "E834"], ["C", "E340"], ["N", "E340"]]);
  assert.equal(failures.find(o => o.name === "T").errorStart, source.indexOf("Nat"));
  const child = failures.find(o => o.name === "C");
  assert.match(child.reason, /Untranslated dependency: T/);
  assert.equal(child.errorStart, source.indexOf("extends T") + "extends ".length);
});

test("a theory's name links to its declarations, its type of models first, and its generated syntax nowhere", async t => {
  const source = `import hlevels;
theory Things(U < UU0) { M : set U; op(x, y : M) : M; }`;
  const { result } = await checkProgram(t, source, { module });
  assert.deepEqual(result.gaps, []);
  const name = source.indexOf("Things");
  assert.deepEqual(result.links.filter(link => link.start === name + "Things".length || link.start >= source.length), []);
  const atName = result.links.filter(link => link.start >= name && link.start < name + "Things".length);
  assert.deepEqual([...new Set(atName.map(link => link.role))], ["def"]);
  assert.equal(atName[0].name, "Things");
});
