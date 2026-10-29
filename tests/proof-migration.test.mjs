import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { canonicalHasher } from "../tools/canonical-hash.mjs";
import { mapDefinitions, verifyMigration } from "../tools/proof-migration.mjs";
import { identicalRewrites, rewriteModule, typePreservingRewrites } from "../tools/proof-rewrites.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { migrationSourceReader } from "../tools/migration-sources.mjs";
import { checkProgram } from "./check-program.mjs";

const library = name => readFile(new URL(`../archive/first-library/${name}.cubist`, import.meta.url), "utf8");
const original = `import primes; use unat;
def moved(C : UNat -> U0, p : 0 + 0 = 0, v : C(0 + 0)) : C(0) {
  exact transport(C, 0 + 0, 0, p, v);
}
def evaluated(A : U0, x, y : A, p : x = y) := at(p, 0);
def two : 1 + 1 = 2 {
  exact refl(2);
}
def mirror(U < UU0, A : U, x, y : A, p : x = y) : y = x {
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
  const lam = (name, body) => ({ tag: "Lam", name, domain: { tag: "Unit" }, body });
  const variable = name => ({ tag: "Var", name });
  assert.equal(hash(lam("x", lam("y", variable("x")))), hash(lam("a", lam("b", variable("a")))));
  assert.notEqual(hash(lam("x", lam("y", variable("x")))), hash(lam("x", lam("y", variable("y")))));
  assert.equal(hash(lam("x", lam("x", variable("x")))), hash(lam("x", lam("y", variable("y")))));
  const line = (dim, formula) => ({ tag: "PLam", dim, family: { tag: "Unit" },
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
  const report = await verify(original.replace("exact transport(C, 0 + 0, 0, p, v);", "exact transport v along p in C;")
    .replace("at(p, 0)", "p @ 0").replace("at(p, flip(i))", "p @ flip(i)"), "identical");
  assert.deepEqual(report.failures, []);
  // mirror is universe-generic: one definition, compared like the others.
  assert.equal(report.identical, 4);
});

test("a changed proof passes only the type level, and a changed statement fails", async () => {
  const proof = original.replace("exact refl(2);", "rfl;");
  assert.deepEqual((await verify(proof, "identical")).failures.map(failure => failure.name), ["two"]);
  const typed = await verify(proof, "types");
  assert.deepEqual(typed.failures, []);
  assert.equal(typed.typesPreserved, 1);
  // 2 = 2 would still convert to 1 + 1 = 2; this statement genuinely differs.
  const statement = await verify(original.replace("def two : 1 + 1 = 2 {\n  exact refl(2);",
    "def two : forall n : UNat. n = n {\n  intro n;\n  rfl;"), "types");
  assert.match(statement.failures.find(failure => failure.name === "two")?.reason ?? "", /public type changed/);
});

test("syntax rewrites keep comments and verify at their declared level", async () => {
  const source = `import paths_; use unat;
def moved(C : UNat -> U0, p : 0 = 0, q : 0 = 0, v : C(0)) : forall a, b, c : UNat. C(0) {
  intro a;
  intro b; // kept apart by this comment
  intro c;
  let h : C(0) {
    exact transport(C, 0, 0, p, v);
  }
  exact h;
}
def pick(A : U0, x, y : A, p : x = y) := (fun (a : A) => fun (b : A) => a)(at(p, 0), y);
def loop(A : U0, x, y : A, p : x = y) : x = x {
  exact concatenate(U0, A, x, y, x, p, inverse_(U0, A, x, y, p));
}
def still(A : U0, x : A) : x = x {
  exact path(fun (i : Interval) => A, fun (i : Interval) => x);
}
def pointed(A : U0, f : A -> A) : f = f {
  exact path(fun (t : Interval) => A -> A, fun (t : Interval, x : A) => f(x));
}
def pointwise(A : U0, f : A -> A) : f = f {
  exact FunExt(U0, A, (fun (a : A) => A), f, f, fun (a : A) => refl(f(a)));
}
`;
  const identical = rewriteModule(source, { rewrites: identicalRewrites });
  assert.deepEqual(identical.applied, { params: 1, intro: 1, let: 1, transport: 1, "path-apply": 1, fun: 1 });
  assert.match(identical.source, /\(C : UNat -> U0, p, q : 0 = 0, v : C\(0\)\)/);
  assert.match(identical.source, /intro a, b; \/\/ kept apart by this comment\n  intro c;/);
  assert.match(identical.source, /let h : C\(0\) := transport v along p in C;/);
  assert.match(identical.source, /\(fun \(a, b : A\) => a\)\(p @ 0, y\)/);
  const typed = rewriteModule(source, { rewrites: typePreservingRewrites });
  assert.deepEqual(typed.applied, { wrappers: 2, "path-lambda": 2, ext: 1, rfl: 1 });
  assert.match(typed.source, /exact trans\(p, sym\(p\)\);/);
  assert.match(typed.source, /exact path i => x;/);
  // Binder groups sharing the interval's fun token stay in a lambda.
  assert.match(typed.source, /exact path t => fun \(x : A\) => f\(x\);/);
  assert.match(typed.source, /ext a;\s+rfl;/);
  const check = async (edited, level) => (await verifyMigration({ modules: ["rewrite_fixture"], level,
    readOriginal: name => name === "rewrite_fixture" ? source : library(name),
    readEdited: async () => formatCubist(edited) }))[0];
  const exact = await check(identical.source, "identical");
  assert.deepEqual(exact.failures, []);
  assert.equal(exact.identical, 6);
  assert.deepEqual((await check(typed.source, "types")).failures, []);
});

test("a rewrite under a projection keeps the projected operand whole", async () => {
  const source = `import unat; use unat;
def applied(p, q : UNat and UNat, e : p = q) : UNat := at(e, 0).1;
def moved(x, y : UNat, e : x = y, v : UNat and Unit) : UNat := transport(fun (n : UNat) => UNat and Unit, x, y, e, v).1;
def picked : UNat := (fun (x : UNat) => fun (y : UNat) => typed(UNat and UNat, (x, y)))(1, 2).2;
`;
  const identical = rewriteModule(source, { rewrites: identicalRewrites });
  assert.deepEqual(identical.applied, { "path-apply": 1, transport: 1, fun: 1 });
  // e @ 0.1 would read as e @ (0.1), which is no interval coordinate.
  assert.match(identical.source, /:= \(e @ 0\)\.1;/);
  assert.match(identical.source, /:= \(transport v along e in \(fun \(n : UNat\) => UNat and Unit\)\)\.1;/);
  assert.match(identical.source, /:= \(fun \(x, y : UNat\) => typed\(UNat and UNat, \(x, y\)\)\)\(1, 2\)\.2;/);
  const [report] = await verifyMigration({ modules: ["projection_fixture"], level: "identical",
    readOriginal: name => name === "projection_fixture" ? source : library(name),
    readEdited: async () => formatCubist(identical.source) });
  assert.deepEqual(report.failures, []);
  assert.equal(report.identical, 3);
  // A library wrapper becomes a call, which a projection applies to as it is.
  const wrapped = rewriteModule("def w := concatenate(U0, A, x, y, z, p, q).1;\n", { rewrites: typePreservingRewrites });
  assert.equal(wrapped.source, "def w := trans(p, q).1;\n");
});

test("a rewrite under a prefix ~ keeps its operand whole", async () => {
  const source = `import unat; use unat;
def reversed_at(A : U0, x, y : A, p, q : x = y, e : p = q) : y = x := ~at(e, 0);
def concatenated_at(A : U0, x, y : A, p, q : x = y, e : p = q) : x = x := at(e, 0) ++ ~at(e, 1);
`;
  const identical = rewriteModule(source, { rewrites: identicalRewrites });
  assert.deepEqual(identical.applied, { "path-apply": 3 });
  // ~e @ 0 would read as (~e) @ 0: a path from y to x in the other direction.
  assert.match(identical.source, /:= ~\(e @ 0\);/);
  assert.match(identical.source, /:= e @ 0 \+\+ ~\(e @ 1\);/);
  const [report] = await verifyMigration({ modules: ["prefix_fixture"], level: "identical",
    readOriginal: name => name === "prefix_fixture" ? source : library(name),
    readEdited: async () => formatCubist(identical.source) });
  assert.deepEqual(report.failures, []);
  assert.equal(report.identical, 2);
});

// A snapshot is named as every display is (forSource), without symbols:
// induction prints as induction, its motive's variable and its predecessor
// one name, though the motive and the successor clause each bind the
// other's name, and the text reads back as the same function.
test("a snapshot prints induction as the source does", async t => {
  const before = `import unat;
use unat;
def f(n : UNat) : forall k : UNat. n = n := induction n as m return forall k : UNat. m = m { zero => fun k => refl(0); succ(k) with ih => fun (m : UNat) => refl(succ(k)); };
`;
  const after = before.replace("fun k => refl(0)", "fun k => (fun (p : 0 = 0) => p)(refl(0))");
  const [report] = await verifyMigration({ modules: ["snapshot_fixture"], level: "types",
    readOriginal: name => name === "snapshot_fixture" ? before : library(name), readEdited: async () => after });
  assert.deepEqual(report.failures, []);
  for (const { text } of [report.changes[0].oldValue, report.changes[0].newValue]) {
    assert.match(text, /^fun \(n : UNat\) => induction n as k return /, text);
    const { result } = await checkProgram(t, `${before}def back : forall n : UNat. forall k : UNat. n = n := ${text};
def same : back = f := refl(f);
`);
    assert.deepEqual(result.gaps, [], text);
  }
});

// A snapshot shows a definition by its name: d0, named as the dimension
// decoding gives f's path, which is renamed, shows as d0 in both
// snapshots, whose hashes tell the two values apart, and each text reads
// back as its side's f.
test("a snapshot shows a definition by its name, as each side defines it", async t => {
  const before = `inductive Circle {
  base;
  loop : base = base;
}
def l : base = base := loop;
def d0 : base = base := l;
def f : base = base := path i => d0 @ i;
`;
  const after = before.replace("def d0 : base = base := l;", "def d0 : base = base := path j => l @ ~j;");
  const [report] = await verifyMigration({ modules: ["unfold_fixture"], level: "types",
    readOriginal: name => name === "unfold_fixture" ? before : library(name), readEdited: async () => after });
  assert.deepEqual(report.failures, []);
  const change = report.changes.find(change => change.declaration === "f");
  for (const [source, { text }] of [[before, change.oldValue], [after, change.newValue]]) {
    const { result } = await checkProgram(t, `${source}def back : base = base := ${text};
def same : back = f := refl(f);
`);
    assert.deepEqual(result.gaps, [], text);
  }
  assert.equal(change.oldValue.text, "path i => d0 @ i");
  assert.equal(change.newValue.text, change.oldValue.text);
  assert.notEqual(change.newValue.hash, change.oldValue.hash);
});

test("dependents are checked against edited definitions they mention", async () => {
  const originals = {
    // n + 0 does not reduce for a variable n, so the edited pick is not
    // convertible with the original.
    dependency_fixture: `import primes; use unat;
def double(n : UNat) := n + n;
def four : double(2) = 4 {
  exact refl(4);
}
def pick(n : UNat) := n + 0;
`,
    dependent_fixture: `import dependency_fixture; use unat;
def same(n : UNat) : pick(n) = pick(n) {
  rfl;
}
def eight : double(4) = 8 {
  rfl;
}
`,
  };
  const edited = { ...originals, dependency_fixture: originals.dependency_fixture
    .replace("exact refl(4);", "rfl;").replace("n + 0;", "n;") };
  const reports = await verifyMigration({ modules: ["dependent_fixture", "dependency_fixture"], level: "types",
    readOriginal: name => originals[name] ?? library(name), readEdited: async name => edited[name] });
  const [dependency, dependent] = reports;
  assert.equal(dependency.module, "dependency_fixture");
  assert.deepEqual(dependency.failures, []);
  assert.equal(dependency.identical, 1);
  assert.equal(dependency.typesPreserved, 2);
  // same mentions the changed pick and no longer has the same type; eight
  // mentions only double, which is identical, so it stays identical.
  assert.deepEqual(dependent.failures.map(failure => [failure.name, failure.reason]),
    [["same", "The public type changed. It mentions changed definitions from: dependency_fixture__pick."]]);
  assert.equal(dependent.identical, 1);
});

// The H1 specification's 6.4: a declaration's kernel extensions under review
// are compared apart from its assumptions. Since H1's release none is under
// review, so starting or stopping to use a declared type changes none. The
// declared type lives in a module the migration leaves unchanged, so both
// versions use one signature.
test("since H1's release, using a declared type adds or removes no kernel extension", async () => {
  const types = "inductive B { yes; no; }\n";
  const plain = "import h1_types;\ndef pick : Unit := tt;\n";
  const declared = "import h1_types;\ndef pick : Unit := (fun (b : B) => tt)(yes);\n";
  const verify = async (original, edited, level) => (await verifyMigration({ modules: ["h1_fixture"], level,
    readOriginal: name => name === "h1_fixture" ? original : name === "h1_types" ? types : library(name),
    readEdited: async () => edited }))[0];
  assert.deepEqual((await verify(plain, declared, "types")).failures, []);
  assert.deepEqual((await verify(declared, plain, "types")).failures, []);
  assert.deepEqual((await verify(declared, declared, "identical")).failures, []);
  // Generative copies now compare through their identical admitted schemas.
  const own = "import unat; use unat;\ninductive C { c; }\ndef one : UNat := 1;\n";
  const report = (await verifyMigration({ modules: ["h1_fixture"], level: "types",
    readOriginal: name => name === "h1_fixture" ? own : library(name), readEdited: async () => own }))[0];
  assert.deepEqual(report.failures, []);
});

test("generative signatures compare bound names and preserve constructor boundaries", async () => {
  const before = `inductive Edge(U < UU0, A : U) { first(a : A); second(a : A); edge(a : A) : first(a) = second(a); }
def pick(A : U0, a : A) : Edge(U0, A) := first(a);
`;
  const verify = async after => (await verifyMigration({modules:["generative"],
    readOriginal:async name => name === "generative" ? before : library(name),readEdited:async () => after}))[0];
  assert.deepEqual((await verify(before)).failures,[]);
  const renamed = before.replaceAll("A : U)","Carrier : U)").replaceAll("a : A);","a : Carrier);")
    .replace("edge(a : A)","edge(a : Carrier)");
  assert.deepEqual((await verify(renamed)).failures,[]);
  const changed = await verify(before.replace("first(a) = second(a)","second(a) = first(a)"));
  assert.match(changed.failures.find(item => item.name === "Edge").reason,/admitted signature changed/);
});

// A baseline read from the archive, and the foundation its edit moves to,
// trunc_types, from the library.
const baseline = (module, before, types) => migrationSourceReader(async (place, name) =>
  place === "archive" && name === module ? before : place === "library" && name === "trunc_types" ? types : null, [module]);

// G4: the same checked migration succeeds only with its exact ledger entry.
test("G4: an exact ledger records a changed public type, and no marker since H1's release", async () => {
  const types = "inductive Tr(A : U0) : prop { point(a : A); }\n";
  const before = "import trunc_types;\ndef value(A : U0, a : A) : A := a;\n";
  const after = "import trunc_types;\ndef value(A : U0, a : A) : Tr(A) := point(a);\n";
  const verify = async (ledger=null,edited=after) => (await verifyMigration({modules:["ledger_fixture"],ledger,
    readOriginal:baseline("ledger_fixture",before,types),readEdited:async () => edited}))[0];
  const strict = await verify();
  assert.match(strict.failures[0].reason,/checked term changed/);
  const change = {...strict.changes[0],remedyGroup:1};
  assert.deepEqual(change.assumptionsRemoved,[]);
  assert.deepEqual(change.extensionsAdded,[]);
  const ledger = {version:2,changes:[change]};
  const allowed = await verify(ledger);
  assert.deepEqual(allowed.failures,[]);
  assert.equal(allowed.ledgerAccepted,1);
  for (const field of ["oldPublicType","newPublicType","oldValue","newValue","assumptionsRemoved","extensionsAdded","hypothesesAdded"]) {
    const altered = structuredClone(ledger);
    if (field.endsWith("PublicType") || field.endsWith("Value")) altered.changes[0][field].hash = "0".repeat(40);
    // A ledger that claims a marker, or a removed assumption, the result
    // lacks is refused too.
    else altered.changes[0][field] = field === "hypothesesAdded" ? ["extra"] : field === "extensionsAdded" ? ["H1"] : ["Truncate"];
    assert.match((await verify(altered)).failures[0].reason,new RegExp(field));
  }
  assert.match((await verify(ledger,after.replace("a : A)","a : A, extra : Unit)"))).failures[0].reason,
    /newPublicType|hypothesesAdded/);
  await assert.rejects(verify({...ledger,changes:[change,change]}),/Duplicate ledger/);
  await assert.rejects(verify({version:2,changes:[{...change,assumptionsRemoved:["LEM"]}]}),/only the four legacy/);
  await assert.rejects(verify({version:2,changes:[{...change,remedyGroup:5}]}),/waits for H2/);
});

test("a ledger never admits a failed declaration or bypasses identical proof verification", async () => {
  const original = "import unat; use unat;\ndef n : UNat := 0;\n", edited = "import unat; use unat;\ndef n : UNat := 1;\n";
  const run = async (after,ledger=null) => (await verifyMigration({modules:["pin"],ledger,
    readOriginal:async name => name === "pin" ? original : library(name),readEdited:async () => after}))[0];
  const initial = await run(edited);
  const ledger = {version:2,changes:[{...initial.changes[0],remedyGroup:1}]};
  assert.match((await run(edited,ledger)).failures[0].reason,/ordinary verification for proof changes/);
  assert.match((await run("import unat; use unat;\ndef n : UNat := tt;\n",ledger)).failures[0].reason,/No longer checks/);
});

test("a pinned type construction can change when both versions already use H1",async()=>{
  const before="import unat; use unat;\ndef Carrier(n : UNat) : U0 := Unit;\n";
  const after="import unat; use unat;\ndef Carrier(n : UNat) : U0 := Unit or Unit;\n";
  const run=async(edited=after,ledger=null)=>(await verifyMigration({modules:["type_value"],ledger,
    readOriginal:name=>name==="type_value"?before:library(name),readEdited:async()=>edited}))[0];
  const strict=await run();
  assert.match(strict.failures[0].reason,/checked term changed/);
  const change={...strict.changes[0],remedyGroup:1};
  assert.equal(change.oldPublicType.hash,change.newPublicType.hash);
  assert.deepEqual(change.extensionsAdded,[]);
  assert.deepEqual(change.extensionsRetained,[]);
  const ledger={version:2,changes:[change]};
  assert.deepEqual((await run(after,ledger)).failures,[]);
  assert.match((await run(after.replace("Unit or Unit","Void"),ledger)).failures[0].reason,/newValue/);
});

test("ledger value pins refuse a different predicate with the same public type and dependencies", async () => {
  const types = "inductive Tr(A : U0) : prop { point(a : A); }\n";
  const before = "import trunc_types;\ndef Predicate(A : U0) := A;\n";
  const after = "import trunc_types;\ndef Predicate(A : U0) := Tr(A);\n";
  const run = async (edited=after, ledger=null, foundation=types) => (await verifyMigration({modules:["meaning"],ledger,
    readOriginal:baseline("meaning",before,foundation),readEdited:async () => edited}))[0];
  const change = {...(await run()).changes[0],remedyGroup:1};
  const ledger = {version:2,changes:[change]};
  assert.deepEqual((await run(after,ledger)).failures,[]);
  const different = await run(after.replace("Tr(A)","Tr(Unit)"),ledger);
  assert.equal(different.changes[0].newPublicType.hash,change.newPublicType.hash);
  assert.deepEqual(different.changes[0].assumptionsRemoved,change.assumptionsRemoved);
  assert.match(different.failures[0].reason,/newValue/);
  const changedSchema = await run(after,ledger,types.replace("point(a : A)","point(a : Unit)"));
  assert.match(changedSchema.failures[0].reason,/newValue/);
  const reordered = structuredClone(ledger);
  for (const key of ["oldPublicType","newPublicType","oldValue","newValue"]) {
    const {hash,text} = reordered.changes[0][key]; reordered.changes[0][key] = {text,hash};
  }
  assert.deepEqual((await run(after,reordered)).failures,[]);
});

test("value pins close over a folded helper even when the public type and displayed value stay unchanged", async () => {
  const types = "inductive Tr(A : U0) : prop { point(a : A); }\n";
  const before = "import trunc_types;\ndef Carrier(A : U0) := A;\ndef Predicate(A : U0) : U0 := Carrier(A);\n";
  const after = "import trunc_types;\ndef Carrier(A : U0) := Tr(A);\ndef Predicate(A : U0) : U0 := Carrier(A);\n";
  const run = async (edited=after,ledger=null) => (await verifyMigration({modules:["closure"],ledger,
    declarations:{closure:["Predicate"]},readOriginal:baseline("closure",before,types),
    readEdited:async () => edited}))[0];
  const change = {...(await run()).changes[0],remedyGroup:1}, ledger={version:2,changes:[change]};
  assert.deepEqual((await run(after,ledger)).failures,[]);
  const altered = await run(after.replace("Tr(A)","Tr(Unit)"),ledger);
  assert.equal(altered.changes[0].newPublicType.hash,change.newPublicType.hash);
  assert.equal(altered.changes[0].newValue.text,change.newValue.text);
  assert.match(altered.failures[0].reason,/newValue/);
});

test("ledgered public dependencies cannot be hidden outside a declaration scope", async () => {
  const types = "inductive Tr(A : U0) : prop { point(a : A); }\n";
  const before = "import trunc_types;\ndef Predicate(A : U0) := A;\ndef witness_(A : U0, a : A) : Predicate(A) := a;\n";
  const after = "import trunc_types;\ndef Predicate(A : U0) := Tr(A);\ndef witness_(A : U0, a : A) : Predicate(A) := point(a);\n";
  const run = async (ledger=null,declarations=null) => (await verifyMigration({modules:["scope"],ledger,declarations,
    readOriginal:baseline("scope",before,types),readEdited:async () => after}))[0];
  const entries = (await run()).changes.map(change => ({...change,remedyGroup:1}));
  assert.deepEqual((await run({version:2,changes:entries})).failures,[]);
  const scoped = await run({version:2,changes:[entries[1]]},{scope:["witness_"]});
  assert.match(scoped.failures[0].reason,/Ledger dependency scope__Predicate is outside.*scope/);
  const unpinned = await run({version:2,changes:[entries[1]]});
  assert.match(unpinned.failures.find(item => item.name === "witness_").reason,/must be identical or have its own verified ledger entry/);
});

// The ledger permits a replacement of a removed legacy builtin by the
// library's axiom of its name, LEM[Truncate] by LEM, only as listed and
// pinned: one the change does not make is refused, and so is any other.
test("a ledger's replacements are exact and its policy's, and its retired comparisons are refused", async () => {
  const types = "inductive Tr(A : U0) : prop { point(a : A); }\n";
  const before = "import trunc_types;\ndef Predicate(A : U0) := A;\n";
  const after = "import trunc_types;\ndef Predicate(A : U0) := Tr(A);\n";
  const run = async ledger => (await verifyMigration({modules:["replacement"],ledger,
    readOriginal:baseline("replacement",before,types),readEdited:async () => after}))[0];
  const change = {...(await run(null)).changes[0],remedyGroup:6};
  assert.deepEqual(change.assumptionsReplaced,[]);
  assert.deepEqual((await run({version:2,changes:[change]})).failures,[]);
  assert.match((await run({version:2,changes:[{...change,assumptionsReplaced:[{old:"LEM[Truncate]",new:"LEM"}]}]})).failures[0].reason,
    /assumptionsReplaced/);
  await assert.rejects(run({version:2,changes:[{...change,assumptionsReplaced:[{old:"LEM[Truncate]",new:"Choice"}]}]}),
    /may replace only LEM\[Truncate\] and Choice\[Truncate\]/);
  const retired = changes => [{comparison:"replacement",lastPassing:"21f55b55",reason:"Retired.",changes}];
  await assert.rejects(run({version:2,changes:[change],retired:retired([])}),
    /belongs to the retired replacement comparison/);
  await assert.rejects(run({version:2,changes:[],retired:retired([change])}),
    /The ledger retired its replacement comparison, which last passed at 21f55b55: Retired\./);
});

test("pinned source resolution keeps archive imports isolated from library collisions", async () => {
  const archive = new Map([["root","import collision;\ndef n : UNat := value;\n"],["collision","import unat; use unat;\ndef value : UNat := 1;\n"]]);
  const rebuilt = new Map([["collision","inductive H { point; }\n"]]);
  const read = async (place,name) => (place === "archive" ? archive : rebuilt).get(name) ?? null;
  const original = migrationSourceReader(read,["root"]);
  const edited = async name => archive.get(name);
  edited.placeOf = () => "archive";
  const report = (await verifyMigration({modules:["root"],readOriginal:original,readEdited:edited}))[0];
  assert.deepEqual(report.failures,[]);
  original.place("library_root","library");
  assert.equal(await original("collision","library_root"),rebuilt.get("collision"));
  assert.match(await original.checkImports("root",["collision"]),/loaded collision from library/);
});

// An axiom has no definition to compare: its assumed statement is compared,
// and an unchanged one stands for the original in its dependents, in its own
// module and in another. A changed statement is reported, as are its users.
test("axioms compare by their assumed statements, and stand for the original in their dependents", async () => {
  const client = "import axioms_fixture;\ndef again := use_;\n";
  const run = async (before, after, modules = ["axioms_fixture"]) => verifyMigration({ modules,
    readOriginal: async name => name === "axioms_fixture" ? before : name === "axiom_client" ? client : library(name),
    readEdited: async name => name === "axioms_fixture" ? after : client });
  const source = "def A := axiom Unit;\ndef use_ := A;\ndef Family(U < UU0) := forall X : U. X -> X;\ndef Assumed := axiom Family;\n";
  const same = await run(source, source, ["axioms_fixture", "axiom_client"]);
  assert.deepEqual(same.map(report => report.failures), [[], []]);
  assert.deepEqual(same.map(report => report.identical), [4, 1]);
  const [changed] = await run(source, source.replace("axiom Unit", "axiom Unit -> Unit"));
  assert.deepEqual(changed.failures.map(failure => [failure.name, failure.reason]), [
    ["A", "The axiom's assumed statement changed."],
    ["use_", "Assumptions changed: axioms_fixture::A -> axioms_fixture__migration_check::A"],
  ]);
  const [defined] = await run(source, source.replace("def A := axiom Unit;", "def A := tt;"));
  assert.match(defined.failures[0].reason, /One version assumes this declaration as an axiom, and the other defines it/);
});

// At level types an axiom's statement is compared as a public type is, by
// bounded kernel conversion: (fun (X : U0) => X)(Unit) stands for Unit, and
// the axiom's dependents keep their types. At level identical the statement
// must be the same, and an unconvertible one fails at either level (#317's
// review round 6, finding 2).
test("at level types an axiom's convertible statement stands for the original", async () => {
  const before = "def A := axiom Unit;\ndef use_ := A;\n";
  const run = (after, level) => verifyMigration({ modules: ["axioms_fixture"], level,
    readOriginal: async name => name === "axioms_fixture" ? before : library(name), readEdited: async () => after });
  const convertible = before.replace("axiom Unit", "axiom (fun (X : U0) => X)(Unit)");
  const [types] = await run(convertible, "types");
  // use_'s type is A's statement, so it is preserved too, not identical.
  assert.deepEqual([types.failures, types.typesPreserved, types.identical], [[], 2, 0]);
  const [identical] = await run(convertible, "identical");
  assert.deepEqual(identical.failures[0], { name: "A", reason: "The axiom's assumed statement changed." });
  const [changed] = await run(before.replace("axiom Unit", "axiom Void"), "types");
  assert.deepEqual(changed.failures[0], { name: "A", reason: "The axiom's assumed statement changed." });
  // What a statement relies on is compared first: B's statement mentions A,
  // which no longer stands for the original.
  const chain = "def A := axiom U0;\ndef B := axiom A;\n";
  const [dependent] = await verifyMigration({ modules: ["axioms_fixture"], level: "types",
    readOriginal: async name => name === "axioms_fixture" ? chain : library(name), readEdited: async () => chain.replace("axiom U0", "axiom U1") });
  assert.deepEqual(dependent.failures.map(failure => failure.name), ["A", "B"]);
  assert.match(dependent.failures[1].reason, /^The axiom's statement relies on other assumptions: axioms_fixture::A -> /);
});

// Trust needs exact identity: an unchanged P never vouches for P__x, a
// declaration whose name only begins like P's, whether P is an axiom or a
// definition; the definition's case predates #317 (#317's review round 7,
// finding 1). P__x's type is kept, but what depends on its value is not.
test("an unchanged declaration never vouches for another whose name begins like its own", async () => {
  const run = (before, after) => verifyMigration({ modules: ["axioms_fixture"], level: "types",
    readOriginal: async name => name === "axioms_fixture" ? before : library(name), readEdited: async () => after });
  const changed = source => source.replace("def P__x : U0 := Unit;", "def P__x : U0 := Void;");
  const axiom = "def P := axiom Unit;\ndef P__x : U0 := Unit;\ndef A := axiom P__x;\ndef use_ := A;\n";
  const [axiomReport] = await run(axiom, changed(axiom));
  assert.deepEqual(axiomReport.failures.map(failure => failure.name), ["A", "use_"]);
  const definition = "def P : Unit := tt;\ndef P__x : U0 := Unit;\ndef use_(y : P__x) : P__x := y;\n";
  const [definitionReport] = await run(definition, changed(definition));
  assert.deepEqual(definitionReport.failures.map(failure => failure.name), ["use_"]);
});

// The edited axiom stands for the original as a free variable only: a binder
// of the same spelling keeps its occurrences (#317's review round 2,
// finding 2). Nor does an axiom's assumption take a binder's name.
test("the verifier renames only an axiom's free occurrences, never a binder's", async () => {
  const variable = name => ({ tag: "Var", name });
  const rename = mapDefinitions(name => name, name => name, name => name === "edited" ? "original" : name);
  const term = { tag: "App", fn: { tag: "Lam", name: "edited", domain: { tag: "Unit" }, body: variable("edited") }, arg: variable("edited") };
  assert.deepEqual(rename(term), { ...term, arg: variable("original") });
  const before = "def F(m__migration_check__A : Unit or Unit) : m__migration_check__A = m__migration_check__A := "
    + "refl(m__migration_check__A);\ndef A1 := axiom Unit or Unit;\ndef use_(x : Unit or Unit) : A1 = A1 := refl(A1);\n";
  const after = before.replace("def use_(x : Unit or Unit) : A1 = A1 := refl(A1);", "def use_ := (fun (unused : Unit or Unit) => F)(A1);");
  for (const level of ["types", "identical"]) {
    const [report] = await verifyMigration({ modules: ["m"], level, readOriginal: async name => name === "m" ? before : library(name),
      readEdited: async () => after });
    assert.deepEqual(report.failures.map(failure => failure.name), ["use_"], level);
  }
});
