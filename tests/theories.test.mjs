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
import { testModule } from "./check-program.mjs";

const theories = testModule("theories", { module: await createCubical() });

test("a theory checks as its model type, constructor, projections, parents' models, homomorphisms and isomorphisms", async () => {
  const { program } = await theories();
  const generated = Object.values(program.symbols).filter(info => info.binding.startsWith("theories__Group."))
    .map(info => info.name);
  assert.deepEqual(generated, ["Group.Model", "Group.make", "Group.M", "Group.M_is_set", "Group.mul", "Group.mul_assoc",
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
  const semiring = Object.values(program.symbols).filter(info => info.binding.startsWith("theories__Semiring."))
    .map(info => info.name);
  assert.deepEqual(semiring.slice(0, 12), ["Semiring.Model", "Semiring.make", "Semiring.R", "Semiring.R_is_set",
    "Semiring.add", "Semiring.add_assoc", "Semiring.zero", "Semiring.zero_add", "Semiring.add_zero", "Semiring.add_comm",
    "Semiring.mul", "Semiring.mul_assoc"]);
  assert.ok(semiring.includes("Semiring.additive") && semiring.includes("Semiring.multiplicative"));
});

test("theory syntax parses with its parents, renamings and notations, and formats stably", () => {
  const source = `import hlevels;

theory Monoid {
  sort M : set;
  mul(x, y : M) : M notation x * y;
  one : M;
  law one_mul(x : M) : one * x = x;
}

theory Rig extends additive : Monoid(
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
  [["additive", "Monoid", ["M:=R", "mul:=add +", "one:=zero", "one_mul:=zero_add"]], [null, "Monoid", ["M:=R"]]]);
  assert.equal(formatCubist(source), source);
  const squeezed = "import hlevels;\ntheory Magma { sort M : set; mul(x, y : M) : M notation x * y;\n law idem(x : M) : x * x = x; }\n";
  const formatted = formatCubist(squeezed);
  assert.equal(formatted, "import hlevels;\ntheory Magma {\n  sort M : set;\n  mul(x, y : M) : M notation x * y;\n  law idem(x : M) : x * x = x;\n}\n");
  assert.equal(formatCubist(formatted), formatted);
});

test("the parser refuses a theory's malformed fields", () => {
  const refused = (body, message) => assert.throws(() => parse(`theory T {\n${body}\n}`), message);
  refused("sort M : type;", /A sort is a set or a proposition: sort M : set; or sort P : prop;/);
  refused("sort M : set; mul(x, y : M) : M notation x ++ y;", /A notation is a binary operator: x \+ y, x \* y, x < y or x <= y\./);
  refused("sort M : set; one M;", /Expected ':' and the type of one, as in mul\(x, y : M\) : M;/);
  refused("sort M : set; law unit(x : M) x = x;", /Expected ':' and the type of unit, as in law mul_one\(x : M\) : x \* one = x;/);
  assert.throws(() => parse("theory T {\n  sort M : set;\n"), /Expected '}' to close the theory\./);
  // law, sort and notation are keywords only where a field starts.
  assert.equal(parse("theory T { law : Unit; sort : Unit; }").declarations[0].fields.map(f => f.name.text).join(), "law,sort");
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
  // section is a keyword only where a top-level item starts.
  assert.equal(parse("def f(section : Nat) := section;").declarations[0].name.text, "f");
});
