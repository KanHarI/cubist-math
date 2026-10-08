import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import { historicalSource, reservedBindingRenaming } from "../web/cubist/legacy-syntax.mjs";
import { parse, languageKeywords } from "../web/cubist/parser.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { verifyMigration } from "../tools/proof-migration.mjs";
import { importedDeclarationsReader, migrationSourceReader } from "../tools/migration-sources.mjs";
import { moduleRoots } from "../web/module-resolution.mjs";

const module = await createCubical();
const read = source => historicalSource(source, "history", { implicitNat: false, minusReverses: false });
async function checked(t, source, prints = []) {
  const rewritten = read(source), program = new CubicalProgram(module, sourceReader());
  t.after(() => program.dispose());
  const result = await program.check(rewritten, "history");
  assert.equal(result.complete, true, JSON.stringify(program.gaps));
  assert.deepEqual(program.prints.map(print => print.text), prints);
  return rewritten;
}

test("historical renaming avoids capture and the migration verifier rejects the captured term", async t => {
  const source = "def f(left : Unit or Unit) : Unit or Unit { let left_ : Unit or Unit := right(tt); exact left; }\n"
    + "def g : Unit or Unit := f(left(tt));\nprint(evaluate(g));\n";
  const rewritten = await checked(t, source, ["left(tt)"]);
  assert.match(rewritten, /f\(left__ :/);
  const captured = source.replace(/\bleft\b/g, "left_").replace("f(left_(tt))", "f(left(tt))");
  const [report] = await verifyMigration({ modules: ["history"], readOriginal: async () => rewritten, readEdited: async () => captured });
  assert.ok(report.failures.some(failure => failure.name === "f" && /checked term changed/.test(failure.reason)));
  await checked(t, "def f(left, left_, left__ : Unit) : Unit := left;\nprint(evaluate(f(tt, tt, tt)));", ["tt"]);
});

test("historical importers share fresh names with the declarations they import", async t => {
  const dependency = "def map(x : Unit or Unit) : Unit or Unit := x;";
  const source = "import provider;\ndef f(map_ : Unit or Unit) : Unit or Unit := map(left(tt));\nprint(evaluate(f(right(tt))));";
  const renaming = reservedBindingRenaming([dependency, source]);
  const options = { implicitNat: false, minusReverses: false, renaming };
  const program = new CubicalProgram(module, async () => historicalSource(dependency, "provider", options));
  t.after(() => program.dispose());
  const result = await program.check(historicalSource(source, "history", { ...options, importedNames: ["map"] }), "history");
  assert.equal(result.complete, true, JSON.stringify(program.gaps));
  assert.deepEqual(program.prints.map(print => print.text), ["left(tt)"]);
});

test("historical archive imports find library declarations and keep their checked meaning", async () => {
  const sources = new Map([
    ["library/provider.cubist", "def map(x : Unit) : Unit := x;"],
    ["library/bridge.cubist", "import provider;"],
    ["archive/first-library/history.cubist", "import bridge;\ndef f : Unit := map(tt);"],
  ]);
  const modulePath = (place, name) => `${moduleRoots[place]}${name}.cubist`;
  const importedDeclarationsOf = importedDeclarationsReader({
    available: new Set(sources.keys()), modulePath,
    readSyntax: path => parse(sources.get(path), false, { bindable: [...languageKeywords] }),
  });
  const options = { implicitNat: false, minusReverses: false, renaming: reservedBindingRenaming([...sources.values()]) };
  const readOriginal = migrationSourceReader(async (place, name) => {
    const path = modulePath(place, name), source = sources.get(path);
    return source === undefined ? null : historicalSource(source, name,
      { ...options, importedDeclarations: importedDeclarationsOf(path) });
  }, ["history"]);
  const [report] = await verifyMigration({ modules: ["history"], readOriginal,
    readEdited: async () => "import bridge;\ndef f : Unit := map_(tt);" });
  assert.deepEqual(report.failures, []);
  assert.equal(report.identical, 1);
});

test("historical imports respect archive precedence and library isolation transitively", () => {
  const sources = new Map([
    ["archive/first-library/history.cubist", "import provider; import bridge;\ndef own := tt;"],
    ["archive/first-library/provider.cubist", "def archiveProvider := tt;"],
    ["library/provider.cubist", "def libraryProvider := tt;"],
    ["library/bridge.cubist", "import provider; import archive_only;\ndef bridgeValue := tt;"],
    ["archive/first-library/archive_only.cubist", "def hidden := tt;"],
  ]);
  const importedDeclarationsOf = importedDeclarationsReader({
    available: new Set(sources.keys()),
    modulePath: (place, name) => `${moduleRoots[place]}${name}.cubist`,
    readSyntax: path => parse(sources.get(path)),
  });
  assert.deepEqual(importedDeclarationsOf("archive/first-library/history.cubist").map(item => item.name.text),
    ["archiveProvider", "libraryProvider", "bridgeValue"]);
  assert.deepEqual(importedDeclarationsOf("library/bridge.cubist").map(item => item.name.text), ["libraryProvider"]);
});

test("historical imported theories and functions supply selection and match types", async t => {
  const dependency = "theory Left(U < UU0) { M : U; law : M; }\n"
    + "def echo(s : Unit or Unit) : Unit or Unit := s;\n";
  const source = "import provider;\ntheory Child(U < UU0) extends Left {}\n"
    + "def selected(m : Child(U0)) : m.M { use m; exact law; }\n"
    + "inductive E { left(x : Unit); right(x : Unit); }\n"
    + "def f(s : Unit or Unit) : Unit { match echo(s) { left(x) => { exact x; } right(y) => { exact y; } } }\n";
  const renaming = reservedBindingRenaming([dependency, source]);
  const options = { implicitNat: false, minusReverses: false, renaming };
  const importedDeclarations = parse(dependency, false, { bindable: [...languageKeywords] }).declarations;
  const program = new CubicalProgram(module, async () => historicalSource(dependency, "provider", options));
  t.after(() => program.dispose());
  const result = await program.check(historicalSource(source, "history", { ...options, importedDeclarations }), "history");
  assert.equal(result.complete, true, JSON.stringify(program.gaps));
});

test("historical references use identifier spans inside parentheses and comments", async t => {
  const source = "def f(left : Unit) : Unit := (( // preserve this\n left));\n"
    + "theory T(U < UU0) { M : U; law : M; }\n"
    + "def g(m : T(U0)) : m.M := ((m).law);\nprint(evaluate(f(tt)));";
  const rewritten = await checked(t, source, ["tt"]);
  assert.match(rewritten, /\(\( \/\/ preserve this\n left_\)\)/);
  assert.match(rewritten, /\(\(m\).law_\)/);
});

test("historical named arguments follow user parameters and preserve generated labels", async t => {
  await checked(t, "import hlevels;\n"
    + "def f(map : Unit) : Unit := map;\ndef g : Unit := f(map := tt);\n"
    + "def h{{id : Unit}}(from : Unit) : Unit := from;\ndef k := h{{id := tt}}(from := g);\n"
    + "theory Legacy(U < UU0) { M : U; map : M; }\n"
    + "theory T(U < UU0) { M : set U; }\n"
    + "def identity(m : T(U0)) : T.Hom(m, m) := T.Hom.make(m, m, map := fun (x : m.M) => x);\n"
    + "def applied(m : T(U0), f : T.Hom(m, m), x : m.M) : m.M := f.map(x);\n"
    + "def called(m : T(U0), x : m.M) : m.M := identity(m).map(x);\n"
    + "print(evaluate(k));", ["tt"]);
});

test("historical model selections bind renamed fields within their scope", async t => {
  await checked(t, "theory T(U < UU0) { M : U; law : M; }\n"
    + "def f(m : T(U0)) : m.M { use m; exact law; }\n"
    + "def m : T(U0) := T.make(Unit, tt);\nuse m;\ndef g : Unit := law;\n"
    + "def local(law : Unit) : Unit := law;\nprint(evaluate(f(m)));\nprint(evaluate(g));", ["tt", "tt"]);
});

test("historical sum matches retain the result types of applied functions", async t => {
  await checked(t, "def Side := Unit or Unit;\ndef side_left : Side := left(tt);\ndef side_right : Side := right(tt);\n"
    + "inductive E { left(x : Unit); right(x : Unit); }\n"
    + "def echo(s : Side) : Side := s;\n"
    + "def curried(x : Unit) : Side -> Side := fun (s : Side) => s;\n"
    + "def implicit{{x : Unit}}(s : Side) : Side := s;\n"
    + "def f(s : Side) : Unit { match echo(s) { left(x) => { exact x; } right(y) => { exact y; } } }\n"
    + "def g(s : Side) : Unit { match curried(tt)(s) { left(x) => { exact x; } right(y) => { exact y; } } }\n"
    + "def h(s : Side) : Unit { match implicit{{tt}}(s) { left(x) => { exact x; } right(y) => { exact y; } } }\n"
    + "print(evaluate(f(side_left)));\nprint(evaluate(g(side_right)));", ["tt", "tt"]);
});

test("historical implicit parent labels become fresh explicit labels with matching references", async t => {
  const rewritten = await checked(t, "theory Left(U < UU0) { M : U; }\n"
    + "theory C(U < UU0) extends Left { left_ : M; }\n"
    + "def parent(m : C(U0)) : Left(U0) := m.left;\n"
    + "def field(m : C(U0)) : m.M := m.left_;\n");
  assert.match(rewritten, /extends left__ : Left/);
  assert.match(rewritten, /:= m.left__;/);
  assert.match(rewritten, /:= m.left_;/);
});
