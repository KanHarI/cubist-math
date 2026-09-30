// The H1 acceptance cases that go through the elaborator and the driver
// (docs/roadmaps/h1-signature-specification.md, section 10), where no other
// test names them. Each test names its cases by ID, as 10.10 traces them;
// the kernel's cases are in kernel/tests/test_signatures.c.
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { CubicalKernel } from "../web/cubical-kernel.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { T, substituteDimension } from "../lib/cubical/core.mjs";
import { interval as I, face as F } from "../lib/cubical/lattice.mjs";

const module = await createCubical();
const library = name => readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8");

async function check(t, source, reader = library) {
  const program = new CubicalProgram(module, reader, { experimental: ["h1"] });
  t.after(() => program.dispose());
  const result = await program.check(source, "main");
  return { program, get: name => {
    const found = result.outputs.find(output => output.name === name);
    assert.ok(found, `no declaration ${name}`);
    return found;
  } };
}
const ok = declaration => assert.ok(declaration.verified, `${declaration.name}: ${declaration.reason}`);
const refused = (declaration, pattern) => {
  assert.equal(declaration.verified, false, `${declaration.name} was accepted`);
  assert.match(declaration.reason, pattern);
};
const lowered = /mismatch|universe|not included/i;
const naturals = "inductive N { zero; succ(n : N); }\n";

test("V2, V3, V5, V6, V12: the sort's level counts stored data and relations, never a phantom parameter", async t => {
  const { program, get } = await check(t, `${naturals}
inductive Box(U < UU0, A : U) { mk(n : N); }
def box_small : U0 := Box(U0, N);
def box_large : U0 := Box(U2, U1);
inductive Pair(U, V < UU0, A : U, B : V) { pair(a : A, b : B); }
def pair_at_max : U1 := Pair(U0, U1, N, U0);
def pair_lowered : U0 := Pair(U0, U1, N, U0);
inductive PairLow(U, V < UU0, A : U, B : V) : U { low_pair(a : A, b : B); }
inductive Quotient(U, V < UU0, A : U, R : A -> A -> V) : set {
  class(a : A);
  glue(a, b : A, r : R(a, b)) : class(a) = class(b);
}
def big_relation(a, b : N) : U1 := U0;
def quotient_at_max : U1 := Quotient(U0, U1, N, big_relation);
inductive QuotientLow(U, V < UU0, A : U, R : A -> A -> V) : set U {
  low_class(a : A);
  low_glue(a, b : A, r : R(a, b)) : low_class(a) = low_class(b);
}
inductive Small(U < UU0, A : U) : U0 { wrap(a : A); }
inductive Wrap(U < UU0) : next(U) { hold(B : U); }
def wrap_small : U1 := Wrap(U0);
`);
  // V2: Box's parameter is a phantom: Box(A) lives in U0 at every level.
  for (const name of ["Box", "box_small", "box_large"]) ok(get(name));
  // V3, V5: stored data and a relation count toward the level, max(U, V);
  // declared at U, each is refused at the argument that lives above it.
  for (const name of ["Pair", "pair_at_max", "Quotient", "quotient_at_max"]) ok(get(name));
  refused(get("pair_lowered"), lowered);
  refused(get("PairLow"), /low_pair's argument b lives in a universe above PairLow's declared one/);
  refused(get("QuotientLow"), /low_glue's argument r lives in a universe above QuotientLow's declared one/);
  // V6: lowering is refused at the argument.
  refused(get("Small"), /wrap's argument a lives in a universe above Small's declared one/);
  // V12: a level-dependent signature, with its universe parameter recorded.
  for (const name of ["Wrap", "wrap_small"]) ok(get(name));
  const recorded = name => program.kernel.signature(program.kernel.signatures.get(`main__${name}`).index).recorded;
  assert.equal(recorded("Box"), 0);
  assert.equal(recorded("Wrap"), 1);
});

test("V9, V10, V11: a former as a function, a signature at tier 1, and an instance at a successor level", async t => {
  const { get } = await check(t, `${naturals}
inductive Tr(U < UU0, A : U) : prop { point(a : A); }
def trunc_former : forall U < UU0. U -> U := Tr;
def former_applied : trunc_former(U0, N) = Tr(U0, N) { rfl; }
inductive Big(A : UU0) { wrap(a : A); }
def big_nat : UU0 := Big(N);
def carrier(A : UU0, b : Big(A)) : UU0 := match b { wrap(a) => A; };
def wrap_point(U < UU0, A : U, a : A) : Tr(U, A) := point(a);
def at_next(U < UU0, A : U, a : A) : Tr(next(U), A) := wrap_point(next(U), A, a);
def rebuilt(U < UU0, A : U, t : Tr(U, A)) : Tr(U, A) := match t {
  point(a) => point(a);
  squash(x, y) @ i => Tr.squash(rebuilt(U, A, x), rebuilt(U, A, y)) @ i;
};
def computes(U < UU0, A : U, a : A) : rebuilt(next(U), A, at_next(U, A, a)) = point(a) { rfl; }
`);
  // V9: Tr used as a value is fun (U < UU0, A : U) => Tr(U, A).
  for (const name of ["trunc_former", "former_applied"]) ok(get(name));
  // V10: Big(A : UU0) lives in UU0, and its eliminator's motive in UU1.
  for (const name of ["Big", "big_nat", "carrier"]) ok(get(name));
  // V11: a generic definition instantiated at next(U), and elimination on
  // point computing there.
  for (const name of ["wrap_point", "at_next", "rebuilt", "computes"]) ok(get(name));
});

test("V21, V22, V23, V29: maps between recorded instances, and universes written in the header", async t => {
  const { get } = await check(t, `
inductive Pointed(U < UU0) : next(U) { pt(X : U, x : X); }
def lift(p : Pointed(U0)) : Pointed(U1) := match p { pt(X, x) => pt(X, x); };
def same(p : Pointed(U0)) : Pointed(U1) := p;
inductive PointedLow(U < UU0) : U { low_pt(X : U, x : X); }
inductive Tr(U < UU0, A : U) : prop U { point(a : A); }
inductive SmallTr(A : U1) : prop U0 { small_point(a : A); }
`);
  // V21: a map between instances by match, X : U0 used at U1.
  for (const name of ["Pointed", "lift"]) ok(get(name));
  // V22: a Pointed(U0) value is not a Pointed(U1) value.
  refused(get("same"), /mismatch/i);
  // V23: the stored type lives in next(U), above the declared U.
  refused(get("PointedLow"), /low_pt's argument X lives in a universe above PointedLow's declared one/);
  // V29: an h-level with a written universe; lowering would be resizing.
  ok(get("Tr"));
  refused(get("SmallTr"), /small_point's argument a lives in a universe above SmallTr's declared one/);
});

test("N5, N6, G1: path eta at a constructor, a boundary that does not hold, and no downward resizing", async t => {
  const { get } = await check(t, `
inductive Circle { base; loop : base = base; }
def eta_loop : loop = (path i => loop @ i) { rfl; }
def flat_loop : loop = (path i => base) { rfl; }
inductive Tr(U < UU0, A : U) : prop { point(a : A); }
def resized : U0 := Tr(U1, U0);
`);
  // N5: loop is its eta expansion.
  ok(get("eta_loop"));
  // N6: loop @ i is not base, so loop is not the constant path.
  refused(get("flat_loop"), /Type mismatch: found loop = loop, expected loop = refl\(base\)/);
  // G1: Tr(A) for A : U1 lives in U1, not U0.
  refused(get("resized"), lowered);
});

test("R4: a kernel module of another ABI version is refused", () => {
  assert.throws(() => new CubicalKernel({ _cb_abi_version: () => 2 }), /ABI version 2, but this code expects version 3/);
});

// K6: transport of merid(a) @ r in Susp(A(i)) along ua of a closed
// equivalence, the integers' successor of the winding fixture. The kernel's
// transport, built from the checked definitions, is the hcomp of 3.5, case 2:
// its base is merid at a moved along the line, succ(a); its tubes are φ's,
// here ⊥, and the walls on r = 0 and r = 1; and restricted to either end, the
// hcomp itself is the transported pole, as transporting the restricted
// meridian is.
test("K6: a meridian transported along ua of the integers' successor", async t => {
  const winding = await readFile(new URL("../docs/examples/h1/winding.cubist", import.meta.url), "utf8");
  const { program, get } = await check(t, `${winding.slice(0, winding.indexOf("inductive Circle"))}
inductive Susp(U < UU0, A : U) { north; south; merid(a : A) : north = south; }
def meridian(a : Int) : typed(Susp(U0, Int), north) = south := merid(a);
def line : Int = Int := ua(U0, Int, Int, succ_equiv);
`, sourceReader());
  for (const name of ["succ_equiv", "Susp", "meridian", "line"]) ok(get(name));
  const { checker } = program, none = new Map(), at = new Map([["r", 0]]);
  const ref = name => ({ tag: "DefRef", name: `main__${name}` });
  const susp = A => T.sort("main__Susp", [A], []), Int = T.sort("main__Int"), N = T.sort("main__N");
  const zero = T.constructor(0, N), pos = n => T.app(T.constructor(0, Int), n), succ = n => T.app(T.constructor(1, N), n);
  // transp^i Susp(line @ i) (meridian(pos(zero)) @ r), at r or at an end.
  const moved = end => T.trans("i", susp(T.at(ref("line"), I.variable("i"))), F.bottom,
    T.at(T.app(ref("meridian"), pos(zero)), end === undefined ? I.variable("r") : end ? [[]] : []));
  const checked = (term, dimensions = none) => checker.infer(term, none, dimensions).term;
  const head = checker.nf(checked(moved(), at), at);
  assert.deepEqual([head.tag, head.system.length], ["HComp", 3]);
  assert.deepEqual([head.base.tag, head.base.path.fn.tag, head.base.path.fn.index], ["PApp", "Con", 2]);
  assert.ok(checker.equal(checked(head.base.path.arg, at), pos(succ(zero)), none, at));
  assert.deepEqual(head.system.map(tube => tube.face), [[["r:0"]], [["r:1"]], []]);
  const [north, south] = [0, 1].map(index => T.constructor(index, susp(Int)));
  for (const [end, pole, other] of [[[], north, south], [[[]], south, north]]) {
    const restricted = checked(substituteDimension(head, "r", end));
    assert.ok(checker.equal(restricted, pole, none, none));
    assert.ok(!checker.equal(restricted, other, none, none));
    assert.ok(checker.equal(checked(moved(end.length)), pole, none, none));
  }
});
