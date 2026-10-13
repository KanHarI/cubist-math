import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import createCubical from "../web/dist/cubical.mjs";
import {checkProgram} from "./check-program.mjs";
import {sourceReader} from "../tools/module-sources.mjs";

const module = await createCubical();
const check = (t, source, fixtures = {}, options = {}) => {
  const library = sourceReader();
  return checkProgram(t, source, {module, options,
    reader: (name, importer) => fixtures[name] ?? library(name, importer)});
};

for (const [label, source, original, kind] of [
  ["definition then inductive", "def N : Unit := tt; inductive N : U0 { c; } def client : Unit := N;", "N", "def"],
  ["inductive then definition", "inductive N : U0 { c; } def N : Unit := tt; def client : N := c;", "N", "inductive"],
  ["two definitions", "def N : Unit := tt; def N : U0 := Nat; def client : Unit := N;", "N", "def"],
  ["definition then constructor", "def c : Unit := tt; inductive N : U0 { c; } def client : Unit := c;", "c", "def"],
  ["constructor then definition", "inductive N : U0 { c; } def c : Unit := tt; def client : N := c;", "N", "inductive"],
  ["constructor then type", "inductive N : U0 { c; } inductive c : U0 { other; } def client : N := c;", "N", "inductive"],
  ["definition then theory", "def N : Unit := tt; theory N(U < UU0) { M : set U; } def client : Unit := N;", "N", "def"],
  ["theory then definition", "theory N(U < UU0) { M : set U; } def N : Unit := tt; def client(S : N(U0)) : U0 := S.M;", "N", "def"],
  ["definition then initial", "def N : Unit := tt; initial N : Monoid(U0); def client : Unit := N;", "N", "def"],
  ["initial then definition", "initial N : Monoid(U0); def N : Unit := tt; def client : N := N.one;", "N", "inductive"],
]) test(`FG1 ownership: ${label} keeps the original binding and source`, async t => {
  const prefix = source.includes("Monoid") ? "import hlevels; import algebra; " : "import hlevels; ";
  const {result, get, program} = await check(t, prefix + source);
  assert.equal(get("client").verified, true, JSON.stringify(result.gaps));
  assert.deepEqual(result.gaps.map(g => g.code), ["E872"]);
  assert.equal(result.complete, false);
  assert.equal(get(original).kind, kind);
  assert.ok(get(original).definitionStart < result.gaps[0].start, "the original source location survives the later refusal");
  assert.deepEqual(get("client").axioms, []);
  const payload = program.export();
  const replay = await check(t, payload.source, payload.sources);
  assert.equal(replay.get("client").type, get("client").type);
  assert.deepEqual(replay.result.gaps.map(g => g.code), ["E872"]);
});

test("FG1 ownership: an existing constructor reserves a generated namespace before publication", async t => {
  const {result, program, get} = await check(t, `import hlevels;
theory T(U < UU0) { M : set U; c : M; }
inductive X : U0 { N; }
initial N : T(U0);
def original : X := N;
def independent : Unit := tt;`);
  assert.deepEqual(result.gaps.map(g => g.code), ["E872"]);
  assert.equal(result.complete, false);
  assert.equal(get("independent").verified, true);
  assert.equal(get("original").verified, true);
  assert.equal(program.kernel.signatures.has("main__N"), false);
  assert.ok(![...program.kernel.definitions.keys()].some(key => key.startsWith("main__N.")));
});

test("FG1 ownership: imported names and local parameter shadowing remain legal", async t => {
  const {result} = await check(t, `import fixture;
def N : Unit := tt;
def local(N : Unit) : Unit := N;
def client : Unit := local(N);`, {fixture: "inductive N : U0 { c; }"});
  assert.deepEqual(result.gaps, []);
});

test("FG1 refusal: a constructor collision blocks the local type and other constructors, with or without imports", async t => {
  for(const imported of [false,true]) {
    const source = `${imported ? "import fixture;" : ""}
def c : Unit := tt;
inductive N : U0 { c; c2; }
def original : Unit := c;
def client : N := c2;
def constructor := c2;
def downstream := client;
def N : Unit := tt;
def after := c2;`;
    const {program,result,get} = await check(t,source,{fixture:"inductive N : U0 { c2; }"});
    assert.equal(get("original").verified,true);
    assert.equal(get("N").verified,false);
    assert.equal(program.kernel.signatures.has("main__N"),false);
    assert.deepEqual(result.gaps.map(g=>g.code),["E872","E340","E340","E340","E872","E340"]);
    for(const name of ["client","constructor","downstream","after"]) {
      assert.equal(get(name).verified,false);
      assert.equal(get(name).blockedBy,"main__N");
      assert.equal(get(name).cause,result.gaps[0].reason);
      assert.equal(program.kernel.definitions.has(`main__${name}`),false);
    }
    const payload=program.export(), replay=await check(t,payload.source,payload.sources);
    assert.deepEqual(replay.result.gaps,result.gaps);
    assert.equal(replay.get("client").blockedBy,"main__N");
  }
});

test("FG1 refusal: a refused local Nat cannot verify clients against imported Nat", async t => {
  const {result,get} = await check(t,`import nat;
def zero : Unit := tt;
inductive Nat : U0 { zero; succ(n : Nat); }
def two : Nat := succ(succ(nat.(0)));
def check_two : two = nat.(2) := refl(two);
def original : Unit := zero;`);
  assert.deepEqual(result.gaps.map(g=>[g.name,g.code]),[["Nat","E872"],["two","E340"],["check_two","E340"]]);
  for(const name of ["two","check_two"]) {
    assert.equal(get(name).verified,false);
    assert.equal(get(name).blockedBy,"main__Nat");
    assert.equal(get(name).cause,result.gaps[0].reason);
  }
  assert.equal(get("original").verified,true);
});

test("FG1 refusal: a duplicate type preserves its owner but refuses its new constructors", async t => {
  const {result,get} = await check(t,`import fixture;
def N : Unit := tt;
inductive N : U0 { c2; }
def original : Unit := N;
def client := c2;`,{fixture:"inductive Imported : U0 { c2; }"});
  assert.equal(get("N").verified,true);
  assert.equal(get("original").verified,true);
  assert.deepEqual(result.gaps.map(g=>g.code),["E872","E340"]);
  assert.equal(get("client").blockedBy,"main__N");
  assert.equal(get("client").cause,result.gaps[0].reason);
});

test("FG1 refusal: a duplicate theory blocks imported members while captured references and local models survive", async t => {
  const {result,get,program} = await check(t,`import fixture;
theory Kept(U < UU0) extends T {}
def saved(S : T(U0)) : S.M := S.c;
def T : Unit := tt;
theory T(U < UU0) { M : set U; new_field : M; }
def original : Unit := T;
def projection := T.c;
def identity := T.Hom.id;
def new_member := T.new_field;
def nested := T.Hom.unknown;
theory CapturedFailure(U < UU0) { M : set U; op(x : T.new_field) : M; }
theory Later(U < UU0) extends Kept {}
def inherited(S : Later(U0)) : S.M := S.c;
def captured(S : Kept(U0)) : S.M := saved(S.t);
def local(T : Kept(U0)) : T.M := T.c;`,
  {fixture:"import hlevels; theory T(U < UU0) { M : set U; c : M; }"});
  // The refused theory never expanded: its own member names stay unknown.
  assert.deepEqual(result.gaps.map(g=>[g.name,g.code]),[["T","E872"],["projection","E340"],["identity","E340"],
    ["new_member","E343"],["nested","E340"],["CapturedFailure","E343"]]);
  for(const name of ["projection","identity","nested"]) {
    assert.equal(get(name).blockedBy,"main__T",name);
    assert.equal(get(name).cause,result.gaps[0].reason,name);
  }
  for(const name of ["original","inherited","captured","local"])assert.equal(get(name).verified,true,name);
  assert.ok(program.declarationReferences.get("main__saved").some(r=>r.binding==="fixture__T.c"));
  const payload=program.export(),replay=await check(t,payload.source,payload.sources);
  assert.deepEqual(replay.result.gaps,result.gaps);
  assert.equal(replay.get("captured").verified,true);
});

for(const kind of ["initial","free"]) test(`FG1 refusal: a duplicate ${kind} blocks its imported model and folds`, async t => {
  const declaration=`${kind} N : T(U0)${kind==="free"?" on Unit":""};`;
  const {result,get} = await check(t,`import fixture;
def saved := N.fold;
def N : Unit := tt;
${declaration}
def original : Unit := N;
def model_client := N.model;
def fold_client := N.fold;
def point := N.c;
def missing := N.unknown;
def captured := saved;`, {fixture:`import hlevels; theory T(U < UU0) { M : set U; c : M; } ${declaration}`});
  assert.deepEqual(result.gaps.map(g=>g.code),["E872","E340","E340","E340","E343"]);
  for(const name of ["model_client","fold_client","point"]) {
    assert.equal(get(name).blockedBy,"main__N");
    assert.equal(get(name).cause,result.gaps[0].reason);
  }
  for(const name of ["original","saved","captured"])assert.equal(get(name).verified,true,name);
});

for(const duplicate of ["theory T(U < UU0) { M : U; c : M; }","initial T : P(U0);","free T : P(U0) on Unit;"]) test(
  `FG1 refusal: a duplicate ${duplicate.split(" ")[0]} keeps the fields of an earlier model of its name`, async t => {
  const {result,get} = await check(t,`theory P(U < UU0) { M : U; c : M; g(x : M, y : M) : M; }
def T := P.make(Unit, tt, fun (x : Unit) => fun (y : Unit) => x);
${duplicate}
def client : T.M := T.c;
def applied := T.g(T.c, T.c);
notation via { x + y := T.g(x, y); }
def noted := via.(T.c + T.c);
theory Q(U < UU0) { M : U; op(x : T.M) : M; }`);
  assert.deepEqual(result.gaps.map(g=>[g.name,g.code]),[["T","E872"]]);
  for(const name of ["T","client","applied","noted","Q"])assert.equal(get(name).verified,true,name);
});

test("FG1 refusal: an existing local generated family survives a second theory's refusal", async t => {
  const {result,get} = await check(t,`import hlevels;
theory T(U < UU0) { M : set U; c : M; }
theory T(U < UU0) { M : set U; other : M; }
def projection := T.c;
def identity := T.Hom.id;
def client(S : T(U0)) : S.M := S.c;
def refused := T.other;`);
  assert.deepEqual(result.gaps.map(g=>g.code),["E872","E343"]);
  for(const name of ["T","projection","identity","client"])assert.equal(get(name).verified,true,name);
});

test("FG1: a duplicate is reported once by inline diagnostics and the REPL while the original still works", async t => {
  const {reported} = await import("../tools/inline-errors.mjs");
  const {ReplSession} = await import("../web/repl-session.mjs");
  const source = "def kept : Unit := tt;\ndef kept : U0 := Unit;\ndef client : Unit := kept;";
  const {program, result, get} = await check(t, source);
  assert.equal(get("client").verified, true);
  assert.deepEqual(reported(source, result, "main"), [{line:1, label:"Error",
    text:"E872: Duplicate declaration kept: a declaration in this module already owns that name."}]);
  const {elaboration} = await import("../web/cubical-elaboration.mjs");
  const explained = elaboration(program,"main");
  assert.deepEqual(explained.map(d=>[d.name,d.verified]), [["kept",true],["kept",false],["client",true]]);
  assert.equal(explained[1].source,"def kept : U0 := Unit;");
  const repl = new ReplSession(program, {base:"main"});
  const entry = await repl.entry(source);
  assert.equal(entry.declarations.find(d=>d.name==="client").verified, true);
  assert.deepEqual(repl.failures(entry), [{kind:"error",
    text:"E872: Duplicate declaration kept: a declaration in this module already owns that name."}]);
});

test("FG1: name availability does not turn an unrelated failed value into a generation dependency", async t => {
  const {result, get} = await check(t, `import hlevels;
def x : Unit := Undefined;
theory T(U < UU0) { M : set U; c : M; }
initial N : T(U0);
def client : N := N.c;`);
  assert.deepEqual(result.gaps.map(g=>[g.name,g.code]), [["x","E343"]]);
  assert.equal(get("T.Hom.id").verified, true);
  assert.equal(get("client").verified, true);
});

test("FG1: model notation extensions are separate from ownership and a refused extension preserves the model", async t => {
  const {result, get} = await check(t, `import hlevels; import nat;
theory T(U < UU0) { M : set U; c : M; }
def n := T.make(Nat, nat_is_set, zero);
notation n { numeral(k : Nat) := zero; }
def selected : n.M := n.(7);
notation n { x + y := add(x, y); }
def after : n.M := n.(8);`);
  assert.equal(result.gaps.length, 1);
  assert.equal(result.gaps[0].directive, true);
  assert.match(result.gaps[0].reason, /adds only a numeral or a literal rule/);
  assert.equal(result.complete, false);
  for(const name of ["n","selected","after"])assert.equal(get(name).verified,true);
});

test("FG1 dependency state: failed parents remain dependencies through import and inheritance chains", async t => {
  const {result, get} = await check(t, `import fixture;
theory C(U < UU0) extends P { law again : e = e; }
theory D(U < UU0) extends C {}
initial N : P(U0);
free W : P(U0) on Unit;
def independent : Unit := tt;`, {fixture: `import hlevels;
theory P(U < UU0) { M : set U; e : M; law bad : e = Undefined; }`});
  assert.deepEqual(result.gaps.map(g => [g.name, g.code]), [["P", "E343"], ["C", "E340"], ["D", "E340"], ["N", "E340"], ["W", "E340"]]);
  assert.equal(get("independent").verified, true);
  assert.match(get("C").reason, /dependency: P/);
  assert.match(get("D").reason, /dependency: C/);
  for(const name of ["C","D","N","W"]) {
    assert.equal(get(name).blockedBy,"fixture__P");
    assert.match(get(name).cause,/Untranslated name: Undefined/);
  }
});

test("FG1 dependency state: a group or inductive refused for a failed dependency passes that dependency's root on", async t => {
  const {result, get} = await check(t, `import hlevels;
def Bad : U0 := Undefined;
inductive X : U0 { mk(b : Bad); }
theory P(U < UU0) { M : set U; c : M; op(x : Bad) : M; }
theory C(U < UU0) extends P {}
theory D(U < UU0) extends C {}
def client(S : P(U0)) : Unit := tt;
def built := mk;
initial N : P(U0);
def independent : Unit := tt;`);
  assert.deepEqual(result.gaps.map(g => [g.name, g.code]),
    [["Bad", "E343"], ["X", "E340"], ["P", "E340"], ["C", "E340"], ["D", "E340"], ["client", "E340"], ["built", "E340"], ["N", "E340"]]);
  assert.equal(get("independent").verified, true);
  // Each client's message names what it refers to; its root is Bad's failure.
  assert.match(get("C").reason, /dependency: P/);
  assert.match(get("built").reason, /dependency: mk/);
  for(const name of ["X","P","C","D","client","built","N"]) {
    assert.equal(get(name).blockedBy, "main__Bad", name);
    assert.match(get(name).cause, /Untranslated name: Undefined/, name);
  }
  const groups = result.publications.main, base = groups.find(g => g.id === "P:base");
  assert.equal(base.failedMember, "P");
  assert.equal(base.cause.binding, "main__Bad");
  for(const id of ["P:hom", "P:iso"]) assert.deepEqual(groups.find(g => g.id === id).cause, base.cause, id);
});

const injected = (member, observe = () => {}) => ({
  onDeclaration(moduleName, declaration, result, checker) {
    if (moduleName === "main" && declaration.name.text === member) {
      observe(checker);
      Object.assign(result, {status: "not-translated", reason: "Untranslated name: injected_failure",
        errorStart: declaration.name.start, errorEnd: declaration.name.end});
    }
  },
});
const absentNative = (program, prefix) => {
  for (const collection of [program.kernel.definitions, program.kernel.signatures, program.checker.definitionViews,
    program.checker.genericDefinitions, program.checker.theories, program.checker.theoryProjections, program.checker.notationPrinting])
    assert.ok(![...collection.keys()].some(key => key === prefix || key.startsWith(prefix + ".")), prefix);
  for (const link of program.links) if (link.verified !== false)
    assert.ok(link.binding !== prefix && !link.binding?.startsWith(prefix + "."), "no checked link may survive rollback");
};

test("G7: an injected parent projection failure rolls back its base group and blocks descendants once", async t => {
  let sawCheckedPredecessor = false;
  const {program, result, get} = await check(t, `import hlevels;
theory P(U < UU0) { M : set U; c : M; }
theory Q(U < UU0) extends P {}
theory R(U < UU0) extends Q {}
def independent(S : P(U0)) : S.M := S.c;`, {}, injected("Q.p", checker => {
    sawCheckedPredecessor = checker.kernel.definitions.has("main__Q.c");
  }));
  assert.equal(sawCheckedPredecessor, true, "inject after earlier members were actually admitted");
  assert.deepEqual(result.gaps.map(g => [g.name, g.code]), [["Q", "E343"], ["R", "E340"]]);
  assert.equal(get("Q").failedMember, "Q.p");
  assert.equal(get("independent").verified, true);
  absentNative(program, "main__Q");
  assert.equal(result.publications.main.find(g => g.id === "Q:base").state, "failed");
  assert.equal(result.publications.main.find(g => g.id === "Q:hom").state, "blocked");
});

test("FG1: a late Hom failure preserves the base and removes its complete Hom/Iso interface", async t => {
  let existed = false;
  const {program, result, get} = await check(t, `import hlevels;
theory T(U < UU0) { M : set U; c : M; }
def usable(S : T(U0)) : S.M := S.c;
def refused(S : T(U0)) := T.Hom.id(S);
def independent : Unit := tt;`, {}, injected("T.Hom.compose", checker => {
    existed = checker.kernel.definitions.has("main__T.Hom.id");
  }));
  assert.equal(existed, true);
  assert.equal(get("usable").verified, true);
  assert.equal(get("independent").verified, true);
  assert.deepEqual(result.gaps.map(g => [g.name, g.code]), [["T.Hom", "E343"], ["refused", "E340"]]);
  assert.ok(program.kernel.definitions.has("main__T.c"));
  assert.equal(get("refused").blockedBy,"main__T.Hom.compose");
  assert.match(get("refused").cause,/injected_failure/);
  absentNative(program, "main__T.Hom"); absentNative(program, "main__T.Iso");
  const failed = result.publications.main.find(g => g.id === "T:hom");
  assert.equal(failed.failedMember, "T.Hom.compose");
  // The injected failure is a root of its own.
  assert.deepEqual(failed.cause, {binding: "main__T.Hom.compose", reason: "Untranslated name: injected_failure"});
  assert.equal(result.publications.main.find(g => g.id === "T:base").state, "checked");
});

test("FG1: a failed fold rolls back an already admitted signature, model and fold map", async t => {
  let existed = false, signature;
  const {program, result, get} = await check(t, `import hlevels;
theory T(U < UU0) { M : set U; c : M; }
initial N : T(U0);
def refused : N := N.c;
def independent : Unit := tt;`, {}, injected("N.fold", checker => {
    existed = checker.kernel.definitions.has("main__N.fold_map");
    signature = checker.kernel.signatures.get("main__N");
  }));
  assert.equal(existed, true);
  assert.notEqual(signature, undefined);
  assert.deepEqual(result.gaps.map(g => [g.name, g.code]), [["N", "E343"], ["refused", "E340"]]);
  assert.equal(get("independent").verified, true);
  absentNative(program, "main__N");
  assert.equal(program.kernel.signature(signature.index).constructors.length, 0, "the native signature was actually removed");
});

test("FG1: editing an imported theory invalidates old generated artifacts and rechecks dependents", async t => {
  const library = sourceReader();
  let fixture = "import hlevels; theory T(U < UU0) { M : set U; c : M; }";
  const {program, result} = await checkProgram(t, "import fixture; initial N : T(U0);", {module,
    reader: (name, importer) => name === "fixture" ? fixture : library(name, importer)});
  assert.deepEqual(result.gaps, []);
  assert.ok(program.kernel.signatures.has("main__N"));
  fixture = "import hlevels; theory T(U < UU0) { M : set U; c : M; law bad : c = Undefined; }";
  const refused = await program.check("import fixture; initial N : T(U0);", "main");
  assert.deepEqual(refused.gaps.map(g => [g.name, g.code]), [["T", "E343"], ["N", "E340"]]);
  absentNative(program, "main__N");
  fixture = "import hlevels; theory T(U < UU0) { M : set U; c : M; }";
  const recovered = await program.check("import fixture; initial N : T(U0); def point : N := N.c;", "main");
  assert.deepEqual(recovered.gaps, []);
  assert.ok(program.kernel.signatures.has("main__N"));
  assert.equal(recovered.outputs.find(o => o.name === "point").verified, true);
});

test("FG1: an unchanged importer recovers when a missing or unparseable dependency is repaired", async t => {
  const {CubicalProgram} = await import("../web/cubical-program.mjs");
  const library = sourceReader();
  let fixture = null;
  const program = new CubicalProgram(module, (name, importer) => {
    if(name!=="fixture")return library(name, importer);
    if(fixture===null)throw Error("fixture is temporarily missing");
    return fixture;
  });
  t.after(()=>program.dispose());
  const source = "import fixture; initial N : T(U0); def client : N := N.c;";
  const valid = "import hlevels; theory T(U < UU0) { M : set U; c : M; }";
  for(const [dependency, accepted] of [[null,false],[valid,true],["theory {",false],[valid,true]]) {
    fixture = dependency;
    const result = await program.check(source,"main");
    assert.equal(result.complete, accepted);
    if(accepted) {
      assert.deepEqual(result.gaps, []);
      assert.equal(result.outputs.find(d=>d.name==="client").verified, true);
    } else absentNative(program,"main__N");
  }
});

test("FG1: rolled-back publications keep progress totals consistent", async t => {
  const {CubicalProgram} = await import("../web/cubical-program.mjs");
  const program = new CubicalProgram(module, sourceReader(), injected("T.Hom.compose"));
  t.after(() => program.dispose());
  const progress = [];
  await program.check("import hlevels; theory T(U < UU0) { M : set U; c : M; } def independent : Unit := tt;", "main", event => progress.push(event));
  for (const event of progress) if (event.total !== null) assert.ok(event.completed <= event.total, JSON.stringify(event));
  assert.equal(progress.at(-1).completed, progress.at(-1).total);
});

test("FG1: a failed optional derived operation leaves ordinary fields usable through use", async t => {
  const {program, result, get} = await check(t, `import hlevels;
theory T(U < UU0) { M : set U; c : M; def helper(x : M) : M := x; }
def client(S : T(U0)) : S.M { use S; exact c; }
def identity(S : T(U0)) := T.Hom.id(S);`, {}, injected("T.helper"));
  assert.deepEqual(result.gaps.map(g => [g.name,g.code]), [["T.helper","E343"]]);
  assert.equal(get("client").verified,true);
  assert.equal(get("identity").verified,true);
  absentNative(program,"main__T.helper");
});

test("FG1: an operator or numeral whose derived operation failed reports that operation's failure", async t => {
  const source = `import hlevels; import nat;
theory T(U < UU0) {
  M : set U; c : M; op(x, y : M) : M notation x + y;
  def sub(x, y : M) : M := op(x, y) notation x - y;
  def opposite(x : M) : M := x notation - x;
  def of_nat(n : Nat) : M := c notation numeral;
}
def plus(S : T(U0)) : S.M { use S; exact c + c; }
def minus(S : T(U0)) : S.M { use S; exact c - c; }
def negative(S : T(U0)) : S.M { use S; exact -c; }
def three(S : T(U0)) : S.M { use S; exact 3; }`;
  for (const [member, client] of [["T.sub", "minus"], ["T.opposite", "negative"], ["T.of_nat", "three"]]) {
    const {result, get} = await check(t, source, {}, injected(member));
    assert.deepEqual(result.gaps.map(g => [g.name, g.code]), [[member, "E343"], [client, "E340"]], member);
    assert.equal(get("plus").verified, true);
    assert.match(get(client).reason, new RegExp(`^Untranslated dependency: ${member.replace(".", "\\.")} at `));
    assert.equal(get(client).blockedBy, `main__${member}`);
    assert.match(get(client).cause, /injected_failure/);
  }
});

test("FG1: observer exceptions roll back the active generated group and permit a fresh check", async t => {
  const {CubicalProgram} = await import("../web/cubical-program.mjs");
  let reject = true;
  const program = new CubicalProgram(module, sourceReader(), {onDeclaration(name, declaration) {
    if(name === "main" && declaration.name.text === "T.c" && reject) {
      reject = false;
      throw Error("observer interrupted publication");
    }
  }});
  t.after(() => program.dispose());
  const source = "import hlevels; def before : Unit := tt; theory T(U < UU0) { M : set U; c : M; } def after : Unit := before;";
  await assert.rejects(program.check(source, "main"), /observer interrupted publication/);
  absentNative(program, "main__T");
  const recovered = await program.check(source, "main");
  assert.deepEqual(recovered.gaps, []);
  assert.equal(recovered.outputs.find(d=>d.name==="after").verified, true);
});
