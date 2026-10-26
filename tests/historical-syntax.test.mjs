import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import { historicalKeywords, historicalSource, reservedBindingRenaming } from "../web/cubist/legacy-syntax.mjs";
import { parse, languageKeywords } from "../web/cubist/parser.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { verifyMigration } from "../tools/proof-migration.mjs";
import { importedDeclarationsReader, migrationSourceReader, historicalModulePaths, historicalMigrationSources, unaryNaturalBase } from "../tools/migration-sources.mjs";
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

// A revision reads `axiom` as it did: one with the axiom form reads current
// sources as written, and one before names something by the word (#317's
// review, finding 3, and round 3, finding 2).
test("historical readers keep current axiom definitions and rename an old binder named axiom", async t => {
  const current = await readFile(new URL("../library/classical_axioms.cubist", import.meta.url), "utf8");
  assert.deepEqual(parse(current, false, { bindable: historicalKeywords({ axiomForm: true }) }).declarations.map(d => d.value.kind),
    ["lambda", "lambda", "axiom", "axiom"]);
  assert.equal(historicalSource(current, "classical_axioms", { implicitNat: false, minusReverses: false, axiomForm: true }), current);
  const rewritten = await checked(t, "def f(axiom : Unit) : Unit := axiom;\ndef axiom := f(tt);\nprint(evaluate(axiom));", ["tt"]);
  assert.match(rewritten, /def f\(axiom_ : Unit\) : Unit := axiom_;\ndef axiom_ := f\(tt\);/);
});

// A historical source that names `axiom` reads the word as that name
// throughout, where the form could stand too, and so does one that imports
// a declaration of that name: no call becomes an assumption (#317's review
// round 2, finding 3).
test("historical sources that bind or import axiom call it, as written then", async t => {
  const source = "def axiom(A : U0) := A;\ndef result := axiom(Unit);\nprint(typeof(result));";
  assert.equal(await checked(t, source, ["U0"]), "def axiom_(A : U0) := A;\ndef result := axiom_(Unit);\nprint(typeof(result));");
  const dependency = "def axiom(A : U0) := A;", importer = "import provider;\ndef result := axiom(Unit);\nprint(typeof(result));";
  const options = { implicitNat: false, minusReverses: false, renaming: reservedBindingRenaming([dependency, importer]) };
  const importedDeclarations = parse(dependency, false, { bindable: [...languageKeywords] }).declarations;
  const program = new CubicalProgram(module, async () => historicalSource(dependency, "provider", options));
  t.after(() => program.dispose());
  const rewritten = historicalSource(importer, "history", { ...options, importedDeclarations });
  assert.equal(rewritten, "import provider;\ndef result := axiom_(Unit);\nprint(typeof(result));");
  const result = await program.check(rewritten, "history");
  assert.equal(result.complete, true, JSON.stringify(program.gaps));
  assert.deepEqual([program.prints.map(print => print.text), result.outputs[0].axioms], [["U0"], []]);
});

// Before the axiom form no revision gave `axiom` a meaning, so a source of
// that time names something by it wherever the word stands: a selected
// model's member, a member after a dot, a qualified declaration. Every
// occurrence is renamed with its declaration, whatever scope supplies it,
// and no call becomes an assumption. A qualified name of any renamed word
// names a declaration, and follows it: provider::left too, which main
// left as it was (#317's review round 3, findings 2 and 3).
test("a revision before the axiom form reads every axiom as the name it was, selected and qualified ones too", async t => {
  const sources = {
    provider: "def axiom(A : U0) : U0 := A;\ndef left(A : U0) : U0 := A;\n",
    models: "theory Provider(U < UU0) { M : U; axiom(A : M) : M; }\n"
      + "def selected : Provider(U1) := Provider.make(U0, fun (A : U0) => A);\n",
    selecting: "import models;\nuse selected;\ndef result := axiom(Unit);\ndef member := selected.axiom(Unit);\n"
      + "print(typeof(result));\nprint(typeof(member));\n",
    qualifying: "import provider;\ndef result := provider::axiom(Unit);\ndef injected := provider::left(Unit);\n"
      + "print(typeof(result));\nprint(typeof(injected));\n",
  };
  const renaming = reservedBindingRenaming(Object.values(sources));
  const options = { implicitNat: false, minusReverses: false, renaming };
  const declarationsOf = name => parse(sources[name], false, { bindable: historicalKeywords() }).items;
  const read = name => historicalSource(sources[name], name, { ...options,
    importedDeclarations: name === "selecting" ? declarationsOf("models") : name === "qualifying" ? declarationsOf("provider") : [] });
  assert.equal(read("selecting"), "import models;\nuse selected;\ndef result := axiom_(Unit);\ndef member := selected.axiom_(Unit);\n"
    + "print(typeof(result));\nprint(typeof(member));\n");
  assert.equal(read("qualifying"), "import provider;\ndef result := provider::axiom_(Unit);\ndef injected := provider::left_(Unit);\n"
    + "print(typeof(result));\nprint(typeof(injected));\n");
  for (const [main, type] of [["selecting", "selected.M"], ["qualifying", "U0"]]) {
    const program = new CubicalProgram(module, async name => read(name));
    t.after(() => program.dispose());
    const result = await program.check(read(main), main);
    assert.equal(result.complete, true, JSON.stringify(program.gaps));
    assert.deepEqual([program.prints.map(print => print.text), result.outputs.map(output => output.axioms)], [[type, type], [[], []]]);
  }
  // The migration verifier tells the call from an explicit axiom.
  const readOriginal = migrationSourceReader(async (place, name) => place === "library" && sources[name] ? read(name) : null, ["selecting"]);
  const [report] = await verifyMigration({ modules: ["selecting"], readOriginal,
    readEdited: async () => "import models;\nuse selected;\ndef result := axiom Unit;\ndef member := selected.axiom_(Unit);\n" });
  assert.deepEqual(report.failures.map(failure => failure.name), ["result"]);
});

// A module's name stands in imports and in qualified names, and both are
// renamed with one plan: a historical module named axiom is axiom_ wherever
// it is named, and the verifier finds it so (#317's review round 4,
// finding 2).
test("a historical module named by a renamed word keeps one name in imports and qualified names", async t => {
  const sources = { axiom: "def f : U0 := Unit;\ndef left(A : U0) : U0 := A;\n",
    history: "import axiom;\ndef result := axiom::f;\ndef injected := axiom::left(Unit);\nprint(typeof(result));\n" };
  const options = { implicitNat: false, minusReverses: false, renaming: reservedBindingRenaming(Object.values(sources)) };
  const declarations = parse(sources.axiom, false, { bindable: historicalKeywords() }).items;
  const read = name => historicalSource(sources[name], name, { ...options, importedDeclarations: name === "history" ? declarations : [] });
  assert.equal(read("history"), "import axiom_;\ndef result := axiom_::f;\ndef injected := axiom_::left_(Unit);\nprint(typeof(result));\n");
  const program = new CubicalProgram(module, async name => name === "axiom_" ? read("axiom") : null);
  t.after(() => program.dispose());
  const result = await program.check(read("history"), "history");
  assert.equal(result.complete, true, JSON.stringify(program.gaps));
  assert.deepEqual(program.prints.map(print => print.text), ["U0"]);
  const readOriginal = migrationSourceReader(async (place, name) => place !== "library" ? null
    : name === "axiom_" ? read("axiom") : name === "history" ? read("history") : null, ["history"]);
  const [report] = await verifyMigration({ modules: ["history"], readOriginal, readEdited: async () => read("history") });
  assert.deepEqual([report.failures, report.identical], [[], 2]);
});

test("historical fill binders leave the box keyword intact", async t => {
  assert.doesNotThrow(() => parse(read("def f(A : U0, a : A, fill : A) : a = a := fun (i : Interval) => fill j in A from a at i { };")));
  const rewritten = await checked(t,
    "def f(A : U0, a : A, fill : A) : A := fill j in A from a at 0 { };\n"
    + "def g(A : U0, fill : A) : A := fill;");
  assert.match(rewritten, /fill_ : A/);
  assert.match(rewritten, /:= fill j in A/);
  assert.match(rewritten, /:= fill_;/);
});

test("historical unannotated owners preserve generated members beside same-named user fields", async t => {
  const rewritten = await checked(t, "import hlevels;\n"
    + "theory Legacy(U < UU0) { M : U; map : M; }\n"
    + "theory T(U < UU0) { M : set U; }\n"
    + "def unannotated(m : T(U0), x : m.M) : T.Hom(m, m) -> m.M := fun h => h.map(x);\n"
    + "def member(m : T(U0), x : m.M) : T.Hom(m, m) -> m.M := fun h => typed(T.Hom(m, m), h).map(x);\n"
    + "def annotated(m : Legacy(U0)) : m.M := m.map;\n"
    + "def projection(m : Legacy(U0)) : m.M := Legacy.map(m);\n");
  assert.match(rewritten, /fun h => h\.map\(x\)/);
  assert.match(rewritten, /:= m\.map_;/);
  assert.match(rewritten, /:= Legacy\.map_\(m\)/);
});

test("historical name planning reads only selected dependency graphs and shares fresh names", () => {
  const sources = new Map([
    ["library/provider.cubist", "def map(x : Unit) : Unit := x;"],
    ["library/history.cubist", "import provider; def f(map_ : Unit) : Unit := map(map_);"],
    ["library/unrelated.cubist", "`this is not tokenizable`"],
  ]);
  const loaded = [], available = new Set(sources.keys());
  const history = historicalMigrationSources({ available, ...historicalModulePaths({ available }),
    readSource: path => { loaded.push(path); return sources.get(path); } });
  const renaming = history.renamingFor(["library/history.cubist"]);
  assert.equal(renaming.map, "map__");
  const rewritten = historicalSource(history.source("library/history.cubist"), "history", {
    implicitNat: false, minusReverses: false, renaming, importedDeclarations: history.importsOf("library/history.cubist"),
  });
  assert.match(rewritten, /:= map__\(map_\)/);
  assert.deepEqual(loaded, ["library/history.cubist", "library/provider.cubist"]);
});

test("historical dependency parse errors name the file and its importer chain", () => {
  for (const invalid of ["def broken := ;", "`not tokenizable`"]) {
    const sources = new Map([
      ["library/history.cubist", "import bridge;"],
      ["library/bridge.cubist", "import broken;"],
      ["library/broken.cubist", invalid],
    ]);
    const available = new Set(sources.keys());
    const history = historicalMigrationSources({ available, ...historicalModulePaths({ available }), readSource: path => sources.get(path) });
    assert.throws(() => history.renamingFor(["library/history.cubist"]),
      /library\/history\.cubist imports bridge: library\/bridge\.cubist imports broken: Cannot read historical module library\/broken\.cubist: (Expected|Unexpected)/);
  }
});

test("historical imports follow relocated library modules with their library resolution", async () => {
  const sources = new Map([
    ["library/history.cubist", "import provider; def f : Unit := map(tt);"],
    ["archive/first-library/provider.cubist", "import leaf; def map(x : Unit) : Unit := x;"],
    ["archive/first-library/leaf.cubist", "def archiveLeaf := tt;"],
    ["library/leaf.cubist", "def libraryLeaf := tt;"],
  ]);
  const available = new Set(sources.keys());
  const paths = historicalModulePaths({ available, movedToLibrary: new Set(["provider"]) });
  const history = historicalMigrationSources({ available, ...paths, readSource: path => sources.get(path) });
  const options = { implicitNat: false, minusReverses: false, renaming: history.renamingFor(["library/history.cubist"]) };
  assert.deepEqual(history.importsOf("library/history.cubist").map(item => item.name.text), ["libraryLeaf", "map"]);
  const readOriginal = migrationSourceReader(async (place, name) => {
    const path = paths.modulePath(place, name);
    return available.has(path) ? historicalSource(history.source(path), name,
      { ...options, importedDeclarations: history.importsOf(path) }) : null;
  }, ["history"]);
  const [report] = await verifyMigration({ modules: ["history"], readOriginal,
    readEdited: async () => "import provider; def f : Unit := map_(tt);" });
  assert.deepEqual(report.failures, []);
  assert.equal(report.identical, 1);
});

test("historical imported notation and simp sets are renamed with their uses", async t => {
  const sources = new Map([
    ["library/provider.cubist", "import unat; notation set { x + y := add(x, y); } simp_set map := [unat_add_zero];"],
    ["library/history.cubist", "import provider; use set; def f(n : UNat) : n + zero = n { simp only [map]; }"],
  ]);
  const available = new Set(sources.keys()), paths = historicalModulePaths({ available });
  const history = historicalMigrationSources({ available, ...paths, readSource: path => sources.get(path) });
  const options = { implicitNat: false, minusReverses: false, renaming: history.renamingFor(["library/history.cubist"]) };
  const fallback = sourceReader();
  const program = new CubicalProgram(module, async (name, importer) => {
    const path = paths.modulePath("library", name);
    return available.has(path) ? historicalSource(history.source(path), name,
      { ...options, importedDeclarations: history.importsOf(path) }) : fallback(name, importer);
  });
  t.after(() => program.dispose());
  const rewritten = historicalSource(history.source("library/history.cubist"), "history",
    { ...options, importedDeclarations: history.importsOf("library/history.cubist") });
  assert.match(rewritten, /use set_;/);
  assert.match(rewritten, /simp only \[map_\]/);
  const result = await program.check(rewritten, "history");
  assert.equal(result.complete, true, JSON.stringify(program.gaps));
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


test("historical unary foundations relocate without changing checked clients", async () => {
  const sources=new Map([
    ["library/nat.cubist", `inductive Nat : U0 { zero; succ(n : Nat); }
      computable def add(a,b : Nat) : Nat := match a { zero => b; succ(n) => succ(add(n,b)); };
      notation nat { x + y := add(x,y); numeral(n : Nat) := n; }`],
    ["archive/first-library/history.cubist", `import nat; use nat;
      def same(n : Nat) : n + 0 = n + 0 := refl(n + 0);`],
  ]);
  const available=new Set(sources.keys()), unaryNat=unaryNaturalBase({available,readSource:p=>sources.get(p)});
  assert.equal(unaryNat,true);
  const paths=historicalModulePaths({available,unaryNat});
  const history=historicalMigrationSources({available,...paths,readSource:p=>sources.get(p)});
  const readOriginal=migrationSourceReader(async (place,name)=>{
    const path=paths.modulePath(place,name);
    return available.has(path)?historicalSource(history.source(path),name==="unat"?"nat":name,
      {implicitNat:false,minusReverses:false,unaryNat,importedDeclarations:history.importsOf(path)}):null;
  },["history"]);
  const [report]=await verifyMigration({modules:["history"],readOriginal,
    readEdited:async()=>`import unat; use unat; def same(n : UNat) : n + 0 = n + 0 := refl(n + 0);`});
  assert.deepEqual(report.failures,[]);
  assert.equal(report.identical,1);
  assert.throws(()=>historicalSource("import nat; def f(UNat : U0) := UNat;","history",
    {implicitNat:false,unaryNat:true}),/would capture existing binding UNat/);
  sources.set("library/unat.cubist","import nat; def UNat : U0 := Void;");
  available.add("library/unat.cubist");
  assert.throws(()=>unaryNaturalBase({available,readSource:p=>sources.get(p)}),/not the identity alias/);
});
