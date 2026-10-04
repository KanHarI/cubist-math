// The H1 acceptance cases that go through the elaborator and the driver
// (docs/roadmaps/h1-signature-specification.md, section 10), where no other
// test names them. Each test names its cases by ID, as 10.10 traces them;
// the kernel's cases are in kernel/tests/test_signatures.c, and those whose
// verdicts are the test are Cubist modules, cubist-tests/h1_acceptance_*.cubist,
// whose comments name them (tests/cubist-tests.test.mjs compares their
// verdicts).
import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalKernel } from "../web/cubical-kernel.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { T, substituteDimension } from "../web/translator/core.mjs";
import { interval as I, face as F } from "../web/translator/lattice.mjs";
import { checkProgram, testModule } from "./check-program.mjs";

const module = await createCubical();
const library = name => readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8");

const check = (t, source, reader = library) => checkProgram(t, source, { module, reader });
const ok = declaration => assert.ok(declaration.verified, `${declaration.name}: ${declaration.reason}`);
const refused = (declaration, pattern) => {
  assert.equal(declaration.verified, false, `${declaration.name} was accepted`);
  assert.match(declaration.reason, pattern);
};
const levels = testModule("h1_acceptance_levels", { module });

// V12: a level-dependent signature records its universe parameter; V2: a
// phantom parameter's universe is not recorded.
test("V2, V12: a phantom parameter's universe is erased, and a level-dependent signature's recorded", async () => {
  const { program } = await levels();
  const recorded = name => program.kernel.signature(program.kernel.signatures.get(`h1_acceptance_levels__${name}`).index).recorded;
  assert.equal(recorded("Box"), 0);
  assert.equal(recorded("Wrap"), 1);
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
