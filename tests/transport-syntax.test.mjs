import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { parse, languageKeywords, reservedNames } from "../web/cubist/parser.mjs";
import { currentTransportSyntax } from "../web/cubist/legacy-transport.mjs";
import { expandedSyntax } from "../web/cubist/tuples.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { verifyMigration } from "../tools/proof-migration.mjs";
import { rewriteModule } from "../tools/proof-rewrites.mjs";
import { checkProgram } from "./check-program.mjs";

const parameters = "A : U0, C : A -> U0, x, y, z : A, p : x = y, q : y = z, v : C(x), f : C(x) -> C(x), vv : C(x) and C(x)";
const forms = [
  ["simple", "transport(C, x, y, p, v)", "transport v along p in C"],
  ["called", "transport(C, x, y, p, f(v))", "transport f(v) along p in C"],
  ["grouped", "transport(C, x, y, p, f(v))", "transport (f(v)) along p in C"],
  ["projected", "transport(C, x, y, p, vv.1)", "transport (vv).1 along p in C"],
  ["applied", "transport(C, x, y, p, (fun (a : C(x)) => a)(v))", "transport (fun (a : C(x)) => a)(v) along p in C"],
  ["tupled", "transport(fun (a : A) => C(a) and C(a), x, y, p, typed(C(x) and C(x), (v, v)))",
    "transport (typed(C(x) and C(x), (v, v))) along p in (fun (a : A) => C(a) and C(a))"],
  ["nested_call", "transport(C, y, z, q, transport(C, x, y, p, v))",
    "transport (transport(C, x, y, p, v)) along q in C"],
  ["nested_syntax", "transport(C, y, z, q, transport(C, x, y, p, v))",
    "transport (transport v along p in C) along q in C"],
  ["in_call", "transport(C, y, z, q, transport(C, x, y, p, v))",
    "transport(C, y, z, q, transport v along p in C)"],
];
const fixture = column => forms.map(row => `def ${row[0]}(${parameters}) := ${row[column]};`).join("\n");

test("along is an ordinary name and a contextual separator in transport and over", async t => {
  assert.equal(languageKeywords.has("along"), false);
  assert.equal(reservedNames.has("along"), false);
  const source = `
def along(A : U0, x : A) : A := x;
def use_along : Unit := along(Unit, tt);
def value_named_along(A : U0, C : A -> U0, x, y : A, p : x = y, along : C(x)) : C(y) :=
  transport along along p in C;
def family_named_along(A : U0, along : A -> U0, x, y : A, p : x = y, v : along(x)) : along(y) :=
  transport v along p in along;
def bridge(A : U0, C : A -> U0, x, y : A, along : x = y, a : C(x), b : C(y),
  q : (transport a along along in C) = b) : PathP(fun (i : Interval) => C(along @ i), a, b) {
  over C along along by { exact q; }
}
`;
  assert.equal(currentTransportSyntax(source), source);
  const formatted = formatCubist(source), { result } = await checkProgram(t, formatted);
  assert.match(formatted, /along\(Unit, tt\)/);
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.ok(result.outputs.every(output => output.verified), JSON.stringify(result.outputs));
  assert.equal(formatCubist(formatted), formatted);
});

test("the retired standalone form is rejected and historical migration preserves its meaning", async () => {
  const old = "along C by p from v";
  assert.throws(() => parse(`def moved(${parameters}) := ${old};`));
  assert.throws(() => parse(`def moved(${parameters}) := along(C) by p from v;`));
  const history = `def moved(${parameters}) := along // family\n C by // path\n p from // value\n v;`;
  const migrated = currentTransportSyntax(history);
  assert.equal(expandedSyntax(parse(migrated)), expandedSyntax(parse(history, false, { historicalTransport: true })));
  for (const comment of ["// family", "// path", "// value"]) assert.ok(migrated.includes(comment));
  const [report] = await verifyMigration({ modules: ["retired_transport"], level: "identical",
    readOriginal: async () => `def moved(${parameters}) := transport(C, x, y, p, v);`,
    readEdited: async () => formatCubist(migrated) });
  assert.deepEqual(report.failures, []);
  assert.equal(report.identical, 1);
});

test("readable, grouped and nested transport forms elaborate identically", async () => {
  const original = fixture(1), edited = formatCubist(fixture(2));
  const [report] = await verifyMigration({ modules: ["transport_fixture"], level: "identical",
    readOriginal: async () => original, readEdited: async () => edited });
  assert.deepEqual(report.failures, []);
  assert.equal(report.identical, forms.length);
  assert.equal(formatCubist(edited), edited);
  assert.match(edited, /transport \(f\(v\)\) along p in C/);
  assert.match(edited, /transport\(C, y, z, q, transport v along p in C\)/);
});

test("transport migration preserves nested calls and tuple operands", async () => {
  const original = fixture(1), edited = rewriteModule(original, { rewrites: ["transport"] }).source;
  assert.match(edited, /transport \(transport v along p in C\) along q in C/);
  const [report] = await verifyMigration({ modules: ["transport_rewrite"], level: "identical",
    readOriginal: async () => original, readEdited: async () => formatCubist(edited) });
  assert.deepEqual(report.failures, []);
  assert.equal(report.identical, forms.length);
});

test("transport requires its delimiters and still checks path and value types", async t => {
  assert.throws(() => parse("def moved := transport v along p;"), /Expected 'in'/);
  assert.throws(() => parse("def moved := transport v in C;"), /Expected 'along'/);
  const { get } = await checkProgram(t, `
def not_a_path := transport tt along tt in (fun (a : Unit) => Unit);
def wrong_fiber(C : Unit -> U0, v : Unit) := transport v along refl(tt) in C;
def heterogeneous(A, B : U0, e : A = B, a : A, b : B, p : PathP(fun (i : Interval) => e @ i, a, b)) :=
  transport tt along p in (fun (v : A) => Unit);
def after : Unit := transport (tt) along refl(tt) in (fun (a : Unit) => Unit);
`);
  assert.equal(get("not_a_path").verified, false);
  assert.match(get("not_a_path").reason, /transport requires a homogeneous base path/);
  assert.equal(get("wrong_fiber").verified, false);
  assert.match(get("wrong_fiber").reason, /[Tt]ype mismatch/);
  assert.equal(get("heterogeneous").verified, false);
  assert.match(get("heterogeneous").reason, /transport requires a homogeneous base path/);
  assert.equal(get("after").verified, true);
});

test("deeply nested explicit calls retain the ordinary call grammar", () => {
  let value = "v";
  for (let depth = 0; depth < 60; depth++) value = `transport(C, x, y, p, ${value})`;
  const source = `def moved := ${value};`;
  assert.doesNotThrow(() => parse(source));
  assert.equal(formatCubist(formatCubist(source)), formatCubist(source));
});
