// `inductive` declarations, work-plan L2.1 (docs/roadmaps/h1-signature-
// specification.md, section 9): the header's result position, lowering to
// the normal form with data before positions, universe classification, the
// least level, uses of the type and its constructors, the experimental gate
// and the `kernel extension: H1` marker (6.4), and the rejections.
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { parse } from "../web/mathscript/parser.mjs";
import { formatMathScript } from "../web/mathscript/formatter.mjs";

const module = await createCubical();
const library = name => readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8");

// Check a program, with other modules by name, and give each declaration's result.
async function check(t, source, { experimental = ["h1"], modules = {} } = {}) {
  const program = new CubicalProgram(module, name => name in modules ? modules[name] : library(name), { experimental });
  t.after(() => program.dispose());
  const result = await program.check(source, "main");
  return { program, result, get: name => {
    const found = result.outputs.find(output => output.name === name);
    assert.ok(found, `no declaration ${name}`);
    return found;
  } };
}
const ok = (declaration, message) => assert.ok(declaration.verified, `${declaration.name}: ${declaration.reason} ${message ?? ""}`);
const refused = (declaration, pattern) => {
  assert.equal(declaration.verified, false, `${declaration.name} was accepted`);
  assert.match(declaration.reason, pattern);
};

const naturals = "inductive N { zero; succ(n : N); }\n";
const lists = "inductive List(U < UU0, A : U) : U { nil; cons(x : A, xs : List(U, A)); }\n";

test("the parser reads each header form, and the formatter keeps them", () => {
  const source = `inductive N { zero; succ(n : N); }
inductive Trunc(U < UU0, A : U) : prop U { point(a : A); }
inductive Flag : U1 { on; off; }
inductive Gpd(U < UU0, A : U) : trunc(1) { point(a : A); }
inductive Circle { base; loop : base = base; }
def prop(set : N) := set;
`;
  const { declarations } = parse(source);
  assert.deepEqual(declarations.map(d => d.kind), ["inductive", "inductive", "inductive", "inductive", "inductive", "def"]);
  assert.deepEqual(declarations.map(d => d.result?.modifier?.kind ?? null), [null, "prop", null, "trunc", null, null]);
  assert.equal(declarations[3].result.modifier.level, 1);
  assert.equal(declarations[2].result.universe.name, "U1");
  assert.equal(declarations[4].constructors[1].type.kind, "binary");
  const formatted = formatMathScript(source);
  assert.match(formatted, /^inductive N \{\n {2}zero;\n {2}succ\(n : N\);\n\}\n\ninductive Trunc/);
  assert.equal(formatMathScript(formatted), formatted);
  for (const [bad, message] of [["inductive X : { a; }", /h-level, a universe or both/],
    ["inductive X : trunc(x) { a; }", /integer level/], ["inductive X { a(U < UU0); }", /bind universes in the declaration's header/],
    ["inductive X { a", /Expected ';'/]])
    assert.throws(() => parse(bad), message);
});

test("declared types need the experimental option, and name it when it is off", async t => {
  const { get } = await check(t, naturals, { experimental: [] });
  refused(get("N"), /kernel extension under review: enable the experimental option h1, with --experimental=h1 in the CLI or Declared types \(H1\) in the workbench/);
  assert.throws(() => new CubicalProgram(module, library, { experimental: ["h9"] }), /Unknown experimental kernel extension: h9/);
});

test("constructors build values, computations hold by rfl, and every result carries the H1 marker", async t => {
  const { get } = await check(t, `${naturals}${lists}
def two : N := succ(succ(zero));
def two_is_two : two = succ(succ(zero)) { rfl; }
def one_two : List(U0, N) := cons(succ(zero), cons(two, nil));
computable def counted : N := two;
def plain : Nat := 2;
`);
  for (const name of ["N", "List", "two", "two_is_two", "one_two", "counted"]) {
    ok(get(name));
    assert.deepEqual(get(name).extensions, ["H1"], `${name} carries the marker`);
    assert.deepEqual(get(name).axioms, [], "the marker is not an assumption");
  }
  assert.deepEqual(get("plain").extensions, []);
  assert.equal(get("one_two").type, "List(N)");
  assert.equal(get("two").type, "N");
});

test("universe parameters: an erased one is read from its parameter, a recorded one carried", async t => {
  const { program, get } = await check(t, `${naturals}${lists}
inductive Pointed(U < UU0) : next(U) { pt(X : U, x : X); }
inductive Lifted(U < UU0) : U { mk; }
def list_small : U0 := List(U0, N);
def list_read : U0 := List(U1, N);
def pointed_small : U1 := Pointed(U0);
def pointed_lowered : U0 := Pointed(U0);
def base_point : Pointed(U0) := pt(N, zero);
def lifted_point : Pointed(U1) := pt(N, zero);
def other_level : Pointed(U1) := base_point;
def lifted : U2 := Lifted(U2);
`);
  const recorded = name => program.kernel.signature(program.kernel.signatures.get(`main__${name}`).index).recorded;
  assert.equal(recorded("List"), 0, "List's universe only bounds A's type");
  assert.equal(recorded("Pointed"), 1, "Pointed stores a type of its own universe");
  assert.equal(recorded("Lifted"), 1, "no parameter can read Lifted's universe");
  // pt(N, zero) is also a Pointed(U1), with N : U0 in U1.
  for (const name of ["list_small", "list_read", "pointed_small", "base_point", "lifted_point", "lifted"]) ok(get(name));
  refused(get("pointed_lowered"), /mismatch|universe|not included/i);
  // Instances at different recorded levels are distinct types.
  refused(get("other_level"), /mismatch/i);
});

test("the sort's level is the least containing its data and arities, or the one written", async t => {
  const { get } = await check(t, `${naturals}
inductive Quotient(U, V < UU0, A : U, R : A -> A -> V) : set {
  class(a : A);
  glue(a, b : A, r : R(a, b)) : class(a) = class(b);
}
def related(a, b : N) : U0 := N;
def big_relation(a, b : N) : U1 := U0;
def small_quotient : U0 := Quotient(U0, U0, N, related);
def large_quotient : U1 := Quotient(U0, U1, N, big_relation);
def large_lowered : U0 := Quotient(U0, U1, N, big_relation);
inductive Flag : U1 { on; off; }
def flag_up : U1 := Flag;
def flag_down : U0 := Flag;
inductive Bad : U0 { mk(X : U0); }
inductive Boxed : prop U1 { box(X : U0); }
`);
  for (const name of ["Quotient", "small_quotient", "large_quotient", "Flag", "flag_up", "Boxed"]) ok(get(name));
  refused(get("large_lowered"), /mismatch|universe|not included/i);
  refused(get("flag_down"), /mismatch|universe|not included/i);
  // Lowering is refused at the constructor, naming the argument.
  refused(get("Bad"), /mk's argument X lives in a universe above Bad's declared one/);
});

test("data are moved ahead of positions, and uses keep the source's order", async t => {
  const { program, get } = await check(t, `${naturals}
inductive Tree(U < UU0, A : U) { leaf; node(l : Tree(U, A), a : A, r : Tree(U, A)); }
def small : Tree(U0, N) := node(leaf, zero, node(leaf, succ(zero), leaf));
def partly : N -> Tree(U0, N) := node(leaf);
def swapped : Tree(U0, N) := node(zero, leaf, leaf);
`);
  ok(get("small"));
  const node = program.kernel.signature(program.kernel.signatures.get("main__Tree").index).constructors[1];
  assert.deepEqual([node.data, node.positions], [1, 2]);
  refused(get("partly"), /Apply node to all its 3 arguments/);
  refused(get("swapped"), /leaf builds Tree\(…\), but N is expected here/);
});

test("higher constructors: paths between constructors, used at coordinates", async t => {
  const { get } = await check(t, `${naturals}
inductive Circle { base; loop : base = base; }
inductive Susp(U < UU0, A : U) { north; south; merid(a : A) : north = south; }
def round : base = base := loop;
def at_end : loop @ 1 = base { rfl; }
def meridian_zero : typed(Susp(U0, N), north) = south := merid(zero);
`);
  for (const name of ["Circle", "Susp", "round", "at_end", "meridian_zero"]) ok(get(name));
});

test("declarations are checked before they are admitted: the rejections name what is wrong", async t => {
  const { get } = await check(t, `${naturals}
inductive Negative { mk(f : Negative -> N); }
inductive Ahead { a : b = b; b; }
inductive Index(U < UU0, A : U) { mk(x : Index(U, N)); }
inductive Word(prop < UU0) { mk; }
inductive Twice { a; a; }
def orphan := nil;
inductive List(U < UU0, A : U) : U { nil; cons(x : A, xs : List(U, A)); }
def needs_type := nil;
def needs_arguments : U0 := List;
`);
  refused(get("Negative"), /sort|position|positiv/i);
  refused(get("Ahead"), /Untranslated name: b|Unbound|b/);
  refused(get("Index"), /own parameters, Index\(U, A\): another argument would be an index/);
  refused(get("Word"), /cannot be named prop/);
  refused(get("Twice"), /a is already a constructor of Twice/);
  refused(get("orphan"), /Untranslated name: nil/);
  refused(get("needs_type"), /nil needs an expected type, to know which List\(…\) it builds/);
  // Alone, List is its former, a function: not a type in U0.
  refused(get("needs_arguments"), /Type mismatch: found forall U < UU0\. U -> U, expected U0/);
});

test("a failed declaration leaves its names untranslated and nothing admitted", async t => {
  const { program, get } = await check(t, `${naturals}
inductive Broken { mk(f : Broken -> N); fine; }
def uses : Broken := fine;
`);
  refused(get("Broken"), /./);
  refused(get("uses"), /Untranslated dependency: (Broken|fine)/);
  assert.equal(program.kernel.signatures.has("main__Broken"), false);
});

test("an imported declared type is used by name, with its marker", async t => {
  const { get } = await check(t, `import numbers;
def three : N := succ(succ(succ(zero)));
def three_again : three = succ(succ(succ(zero))) { rfl; }
`, { modules: { numbers: naturals } });
  ok(get("three"));
  ok(get("three_again"));
  assert.deepEqual(get("three").extensions, ["H1"]);
});

test("computable accepts the marker, and still refuses an assumption, naming it", async t => {
  const { get } = await check(t, `import classical_axioms;
${naturals}
computable def marked : N := succ(zero);
computable def both : N and ExcludedMiddle(U0) := (zero, LEM(U0));
`);
  ok(get("marked"));
  assert.deepEqual(get("marked").extensions, ["H1"]);
  refused(get("both"), /depends on non-computing assumptions: LEM/);
  assert.doesNotMatch(get("both").reason, /H1|kernel extension/);
});

test("a two-dimensional constructor of a type with parameters takes its instance from a square's type", async t => {
  const { get } = await check(t, `${naturals}
inductive Sq(U < UU0, A : U) {
  b;
  l : b = b;
  s : PathP(fun (i : Interval) => l @ i = l @ i, l, l);
}
def loop_n : typed(Sq(U0, N), b) = b := l;
def square : PathP(fun (i : Interval) => loop_n @ i = loop_n @ i, loop_n, loop_n) := s;
`);
  for (const name of ["Sq", "loop_n", "square"]) ok(get(name));
});

test("constructor types are beta-reduced before they are classified and admitted", async t => {
  const { get } = await check(t, `${naturals}
inductive C { b; l : typed(C, b) = b; }
inductive Beta : U0 { mk(x : (fun (X : U0) => N)(Beta)); }
def made : Beta := mk(zero);
`);
  // The ascription's identity redex would not be a constructor expression,
  // and the redex that mentions Beta is data, of type N.
  for (const name of ["C", "Beta", "made"]) ok(get(name));
});

test("binders written in a constructor's result are its arguments", async t => {
  const { program, get } = await check(t, `${naturals}
inductive M { z; s : M -> M; w : N -> M; }
def one : M := s(z);
def lifted : M := w(succ(zero));
`);
  for (const name of ["M", "one", "lifted"]) ok(get(name));
  const shape = program.kernel.signature(program.kernel.signatures.get("main__M").index).constructors;
  assert.deepEqual(shape.map(c => [c.data, c.positions]), [[0, 0], [0, 1], [1, 0]]);
});

test("a type former used as a value is a lambda over its universes and parameters", async t => {
  const { get } = await check(t, `${naturals}${lists}
inductive Pointed(U < UU0) : next(U) { pt(X : U, x : X); }
def former : forall U < UU0. next(U) := Pointed;
def list_former : forall U < UU0. U -> U := List;
def applied : List(U0, N) = list_former(U0, N) { rfl; }
`);
  for (const name of ["former", "list_former", "applied"]) ok(get(name));
});

test("without an expected type, a constructor's instance is read from a position argument", async t => {
  const { get } = await check(t, `${naturals}${lists}
def prepend(xs : List(U0, N)) := cons(zero, xs);
def still_needs := nil;
`);
  ok(get("prepend"));
  assert.equal(get("prepend").type, "(List(N) → List(N))");
  refused(get("still_needs"), /nil needs an expected type/);
});

test("second review: types are checked before reduction, level redexes reduce, telescopes substitute at once", async t => {
  const { get } = await check(t, `${naturals}
inductive Discarded { c(x : (fun (n : Nat) => Nat)(U0)); }
inductive Level { b; c : (fun (U < UU0) => Level)(U0); d(x : (fun (U < UU0) => Nat)(U0)); }
`);
  // The redex's argument U0 is not a Nat: the kernel sees it before reduction drops it.
  refused(get("Discarded"), /mismatch/i);
  ok(get("Level"));
  // Each module numbers its own names: here the importer's B and A get the
  // names the declaration's A and B had, and are still not them.
  const imported = await check(t, "import telescope;\ndef use(dummy : Nat, B : U0, A : U0, b : B) := S(B, A, b);\n",
    { modules: { telescope: "inductive S(A : U0, B : U0, a : A) { c; }\n" } });
  ok(imported.get("use"));
});

test("second review: shape errors name the constructor and its argument, where they are", async t => {
  const source = `${naturals}
inductive Negative { c(x : Negative -> N); }
inductive Nested { c(x : Nested and N); }
inductive Composed { a; p : a = a; q : a = a; s : trans(p, q) = p; }
`;
  const { get } = await check(t, source);
  refused(get("Negative"), /Negative occurs in a negative position: c's argument x takes an argument that mentions Negative/);
  assert.equal(get("Negative").errorStart, source.indexOf("x : Negative"));
  refused(get("Nested"), /c's argument x mentions Nested but is not one/);
  // A boundary with a composition, refused by the kernel (Q3), at its constructor.
  refused(get("Composed"), /Constructor s: /);
  assert.equal(get("Composed").errorStart, source.indexOf("s : trans"));
});

test("second review: inspection shows the marker, and only the result position's words are keywords", async t => {
  const { program } = await check(t, `${naturals}def n : N := zero;\n`);
  assert.deepEqual(program.inspect("main__n").extensions, ["H1"]);
  const { headerWordAt } = await import("../web/source-tokens.mjs");
  const header = "inductive T(x : type) : prop { a; }";
  assert.equal(headerWordAt(header, header.indexOf("type"), "type"), false, "a parameter's type is a name");
  assert.equal(headerWordAt(header, header.indexOf("prop"), "prop"), true);
});
