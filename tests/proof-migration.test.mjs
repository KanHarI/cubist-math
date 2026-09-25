import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { canonicalHasher, verifyMigration } from "../tools/proof-migration.mjs";
import { identicalRewrites, rewriteModule, typePreservingRewrites } from "../tools/proof-rewrites.mjs";
import { formatMathScript } from "../web/mathscript/formatter.mjs";

const library = name => readFile(new URL(`../web/proofs/${name}.cubist`, import.meta.url), "utf8");
const original = `import primes;
def moved(C : Nat -> U0, p : 0 + 0 = 0, v : C(0 + 0)) : C(0) {
  exact transport(C, 0 + 0, 0, p, v);
}
def evaluated(A : U0, x y : A, p : x = y) = at(p, 0);
def two : 1 + 1 = 2 {
  exact refl(2);
}
def mirror(U : Universe, A : U, x y : A, p : x = y) : y = x {
  exact path(fun (i : Interval) => A, fun (i : Interval) => at(p, flip(i)));
}
`;
const verify = async (edited, level) => {
  const [report] = await verifyMigration({ modules: ["migration_fixture"], level,
    readOriginal: name => name === "migration_fixture" ? original : library(name),
    readEdited: async () => edited });
  return report;
};

test("canonical hashes ignore bound names but not binding structure", () => {
  const hash = canonicalHasher();
  const lam = (name, body) => ({ tag: "Lam", name, domain: { tag: "Nat" }, body });
  const variable = name => ({ tag: "Var", name });
  assert.equal(hash(lam("x", lam("y", variable("x")))), hash(lam("a", lam("b", variable("a")))));
  assert.notEqual(hash(lam("x", lam("y", variable("x")))), hash(lam("x", lam("y", variable("y")))));
  assert.equal(hash(lam("x", lam("x", variable("x")))), hash(lam("x", lam("y", variable("y")))));
  const line = (dim, formula) => ({ tag: "PLam", dim, family: { tag: "Nat" },
    body: { tag: "PApp", path: variable("p"), arg: formula } });
  assert.equal(hash(line("i", [["i:1"]])), hash(line("j", [["j:1"]])));
  assert.notEqual(hash(line("i", [["i:1"]])), hash(line("i", [["k:1"]])));
  // A shared subterm first hashed under two binders must hash the same when
  // an equal copy appears at the top level.
  const shared = lam("z", variable("z"));
  hash(lam("a", lam("b", shared)));
  assert.equal(hash(shared), hash(lam("w", variable("w"))));
  // One application node under two different binders of its argument.
  const application = { tag: "App", fn: variable("f"), arg: variable("x") };
  assert.notEqual(hash(lam("x", lam("y", application))), hash(lam("y", lam("x", application))));
});

test("syntax that elaborates to the same terms verifies as identical", async () => {
  const report = await verify(original.replace("exact transport(C, 0 + 0, 0, p, v);", "exact along C by p from v;")
    .replace("at(p, 0)", "p @ 0").replace("at(p, flip(i))", "p @ flip(i)"), "identical");
  assert.deepEqual(report.failures, []);
  assert.equal(report.identical, 4);
  assert.equal(report.templates, 1);
});

test("a changed proof passes only the type level, and a changed statement fails", async () => {
  const proof = original.replace("exact refl(2);", "rfl;");
  assert.deepEqual((await verify(proof, "identical")).failures.map(failure => failure.name), ["two"]);
  const typed = await verify(proof, "types");
  assert.deepEqual(typed.failures, []);
  assert.equal(typed.typesPreserved, 1);
  // 2 = 2 would still convert to 1 + 1 = 2; this statement genuinely differs.
  const statement = await verify(original.replace("def two : 1 + 1 = 2 {\n  exact refl(2);",
    "def two : forall n : Nat, n = n {\n  intro n;\n  rfl;"), "types");
  assert.match(statement.failures.find(failure => failure.name === "two")?.reason ?? "", /public type changed/);
});

test("syntax rewrites keep comments and verify at their declared level", async () => {
  const source = `import paths;
def moved(C : Nat -> U0, p : 0 = 0, q : 0 = 0, v : C(0)) : forall a b c : Nat, C(0) {
  intro a;
  intro b; // kept apart by this comment
  intro c;
  have h : C(0) {
    exact transport(C, 0, 0, p, v);
  }
  exact h;
}
def pick(A : U0, x y : A, p : x = y) = (fun (a : A) => fun (b : A) => a)(at(p, 0), y);
def loop(A : U0, x y : A, p : x = y) : x = x {
  exact concatenate(U0, A, x, y, x, p, inverse(U0, A, x, y, p));
}
def still(A : U0, x : A) : x = x {
  exact path(fun (i : Interval) => A, fun (i : Interval) => x);
}
def pointwise(A : U0, f : A -> A) : f = f {
  exact FunExt(U0, A, (fun (a : A) => A), f, f, fun (a : A) => refl(f(a)));
}
`;
  const identical = rewriteModule(source, { rewrites: identicalRewrites });
  assert.deepEqual(identical.applied, { params: 1, intro: 1, have: 1, along: 1, "path-apply": 1, fun: 1 });
  assert.match(identical.source, /\(C : Nat -> U0, p q : 0 = 0, v : C\(0\)\)/);
  assert.match(identical.source, /intro a b; \/\/ kept apart by this comment\n  intro c;/);
  assert.match(identical.source, /have h : C\(0\) := along C by p from v;/);
  assert.match(identical.source, /\(fun \(a b : A\) => a\)\(p @ 0, y\)/);
  const typed = rewriteModule(source, { rewrites: typePreservingRewrites });
  assert.deepEqual(typed.applied, { wrappers: 2, "path-lambda": 1, ext: 1, rfl: 1 });
  assert.match(typed.source, /exact trans\(p, sym\(p\)\);/);
  assert.match(typed.source, /exact path i => x;/);
  assert.match(typed.source, /ext a;\s+rfl;/);
  const check = async (edited, level) => (await verifyMigration({ modules: ["rewrite_fixture"], level,
    readOriginal: name => name === "rewrite_fixture" ? source : library(name),
    readEdited: async () => formatMathScript(edited) }))[0];
  const exact = await check(identical.source, "identical");
  assert.deepEqual(exact.failures, []);
  assert.equal(exact.identical, 5);
  assert.deepEqual((await check(typed.source, "types")).failures, []);
});
