import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import {readFile} from "node:fs/promises";
import createCubical from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {Translator} from "../web/translator/translate.mjs";
import {ElaborationStop} from "../web/translator/control.mjs";

const wasm = await createCubical();
const readLibrary = name => readFile(new URL(`../library/${name}.cubist`, import.meta.url), "utf8");
const cases = [
  {name: "ordinary declaration", source: "def f : Unit := stop_here;", attempt: null},
  {name: "quiet argument inference", source: "def keep_{{A : U0}}(x : A) : A := x; def f := keep_(stop_here);", attempt: "argument-inference"},
  {name: "quiet constructor inference", source: "inductive Box(A : U0) { box(value : A); } def f := box(stop_here);", attempt: "constructor-inference"},
  {name: "recursive retry", source: "import nat; def f(n, m : Nat) : Nat := match n { zero => stop_here; succ(k) => f(k, m); };", attempt: "recursive-fixed"},
  {name: "written implicit path before fallback", source: "import hlevels; inductive S1 { base; loop : base = base; } inductive Two : prop U0 { left_; right_; } def f(c : S1) : Two := match c { base => left_; _ => stop_here; };", attempt: "implicit-path-body"},
];
for (const scenario of cases) test(`a replay stop escapes ${scenario.name} and rolls back the declaration`, async t => {
  const program = new CubicalProgram(wasm, readLibrary);
  t.after(() => program.dispose());
  const stop = new ElaborationStop({kind: "query", text: "serialized result"});
  const term = Translator.prototype.term;
  let caughtAt = null, visits = 0;
  Translator.prototype.term = function (node, scope, expected) {
    if (node.kind === "name" && node.name === "stop_here") {
      visits++;
      caughtAt = scope.unit.observations.path;
      throw stop;
    }
    return term.call(this, node, scope, expected);
  };
  try {await assert.rejects(program.check(scenario.source, "main"), value => value === stop);}
  finally {Translator.prototype.term = term;}
  assert.equal(visits, 1, "no inference retry or fallback may consume the replay control");
  assert.ok(caughtAt);
  if (scenario.attempt) assert.ok(caughtAt.some(edge => edge.kind === scenario.attempt), JSON.stringify(caughtAt));
  assert.equal(program.kernel.definitions.has("main__f"), false);
  assert.equal(program.checker.definitionViews.has("main__f"), false);
  assert.deepEqual(stop.result, {kind: "query", text: "serialized result"});
});
