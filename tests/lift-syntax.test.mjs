import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { parse, languageKeywords, reservedNames } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { freeNames } from "../web/cubist/scopes.mjs";
import { currentSyntax, renameReservedBindings } from "../web/cubist/legacy-syntax.mjs";
import { verifyMigration } from "../tools/proof-migration.mjs";
import { checkProgram } from "./check-program.mjs";

const parameters = "A : U0, C : A -> U0, x, y : A, p : x = y, a : C(x), b : C(y), q : (transport a along p in C) = b";
const resultType = "PathP(fun (i : Interval) => C(p @ i), a, b)";

test("lift is an expression with the same checked term as the explicit transport bridge", async () => {
  for (const value of ["q", "(q)", "(typed(((transport a along p in C) = b) and Unit, (q, tt))).1"]) {
    const original = `def lifted(${parameters}) : ${resultType} := path_from_transport(fun (i : Interval) => C(p @ i), a, b, ${value});`;
    const edited = formatCubist(`def lifted(${parameters}) : ${resultType} := lift ${value} along (p) in C;`);
    const [report] = await verifyMigration({ modules: ["lift_fixture"], level: "identical",
      readOriginal: async () => original, readEdited: async () => edited });
    assert.deepEqual(report.failures, [], value);
    assert.equal(report.identical, 1);
    assert.equal(formatCubist(edited), edited);
  }
});

test("lift composes with calls, typed values, path expressions and local equality proofs", async t => {
  const source = `
def keep(T : U0, value : T) : T := value;
def direct(${parameters}) : ${resultType} := lift q along p in C;
def argument(${parameters}) : ${resultType} := keep(${resultType}, lift q along p in C);
def endpoint(${parameters}) : C(x) := typed(${resultType}, lift q along p in C) @ 0;
def nested(${parameters}) : ${resultType} :=
  lift (lift path_to_transport(fun (i : Interval) => C(y), transport a along p in C, b, q)
    along refl(y) in (fun (z : A) => C(y))) along p in C;
def local(${parameters}) : ${resultType} {
  let equal_after : (transport a along p in C) = b { exact q; }
  exact lift equal_after along p in C;
}
def reflected(A : U0, C : A -> U0, x, y : A, p : x = y, a : C(x)) :
  PathP(fun (i : Interval) => C(p @ i), a, transport a along p in C) :=
  lift refl(transport a along p in C) along p in C;
def named_along(A : U0, C : A -> U0, x, y : A, p : x = y, a : C(x), b : C(y),
  along : (transport a along p in C) = b) : ${resultType} := lift along along p in C;
def over(T : U0, value : T) : T := value;
def use_over : Unit := over(Unit, tt);
`;
  const formatted = formatCubist(source), { result } = await checkProgram(t, formatted);
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.ok(result.outputs.every(output => output.verified), JSON.stringify(result.outputs));
  assert.equal(formatCubist(formatted), formatted);
  assert.match(formatted, /lift \(\s*lift path_to_transport/);
  assert.equal(reservedNames.has("along"), false);
  assert.equal(reservedNames.has("over"), false);
  assert.equal(languageKeywords.has("lift"), true);
  const syntax = parse("def example := lift q along p in C;").declarations[0].value;
  assert.deepEqual([...freeNames(syntax)].sort(), ["C", "p", "q"]);
});

test("lift checks the base path, equality and the entire expected dependent family", async t => {
  const { get } = await checkProgram(t, `
def unannotated(${parameters}) := lift q along p in C;
def not_a_path(${parameters}) : Unit := lift q along p in C;
def bad_base(${parameters}) : ${resultType} := lift q along tt in C;
def bad_equality(${parameters}) : ${resultType} := lift refl(b) along p in C;
def wrong_endpoint(${parameters}, other : C(y)) : PathP(fun (i : Interval) => C(p @ i), a, other) := lift q along p in C;
def wrong_family(${parameters}, D : A -> U0, aD : D(x), bD : D(y), qD : (transport aD along p in D) = bD) :
  PathP(fun (i : Interval) => D(p @ i), aD, bD) := lift qD along p in C;
def wrong_base_path(${parameters}, r : x = y) : PathP(fun (i : Interval) => C(r @ i), a, b) := lift q along p in C;
def heterogeneous(A, B : U0, e : A = B, a : A, b : B, p : PathP(fun (i : Interval) => e @ i, a, b)) : tt = tt :=
  lift refl(tt) along p in (fun (v : A) => Unit);
def valid_after(${parameters}) : ${resultType} := lift q along p in C;
`);
  for (const name of ["unannotated", "not_a_path"])
    assert.match(get(name).reason, /lift needs an expected Path or PathP type/);
  for (const name of ["bad_base", "heterogeneous"])
    assert.match(get(name).reason, /lift requires a homogeneous base path/);
  for (const name of ["bad_equality", "wrong_endpoint", "wrong_family", "wrong_base_path"])
    assert.equal(get(name).verified, false, name);
  assert.equal(get("valid_after").verified, true, get("valid_after").reason);
});

test("HoTT expression operands do not accept proof blocks and over is retired", () => {
  for (const expression of ["lift { exact q; } along p in C", "lift q along { exact p; } in C",
    "lift q along p in { exact C; }", "transport { exact a; } along p in C",
    "transport a along { exact p; } in C", "transport a along p in { exact C; }", "path i => { exact a; }"])
    assert.throws(() => parse(`def rejected(${parameters}) : ${resultType} := ${expression};`), /Expected an expression/);
  assert.throws(() => parse(`def retired(${parameters}) : ${resultType} { over C along p by { exact q; } }`));
  assert.throws(() => parse("def bad := lift q along p;"), /Expected 'in'/);
});

test("historical over and along migrate together, preserving comments and checked terms", async () => {
  const original = `def lifted(${parameters}) : ${resultType} := path_from_transport(fun (i : Interval) => C(p @ i), a, b, q);`;
  const old = `def lifted(${parameters.replace("transport a along p in C", "along C by p from a")}) : ${resultType} {
    over // family\n C along // base\n p by // proof\n { // start\n exact q; // finish\n }
  }`;
  const edited = formatCubist(currentSyntax(old));
  for (const comment of ["// family", "// base", "// proof", "// start", "// finish"]) assert.ok(edited.includes(comment));
  assert.equal(currentSyntax(edited), edited);
  const [report] = await verifyMigration({ modules: ["lift_fixture"], level: "identical",
    readOriginal: async () => original, readEdited: async () => edited });
  assert.deepEqual(report.failures, []);
  assert.equal(report.identical, 1);
  const renamed = renameReservedBindings("def lift(T : U0, value : T) : T := value; def use_lift : Unit := lift(Unit, tt);", {lift: "lift_"});
  assert.match(renamed, /def lift_\(/);
  assert.match(renamed, /:= lift_\(Unit, tt\)/);
  assert.doesNotThrow(() => parse(renamed));
});
