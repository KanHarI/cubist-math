import test from "node:test";
import assert from "node:assert/strict";
import {parse} from "../web/cubist/parser.mjs";
import {reference, elaborationSyntax} from "../web/cubist/references.mjs";
import {rewritten, freeNames, fixedBinders, renamedFree, substituted, relocated} from "../web/cubist/scopes.mjs";
import {capturedNames} from "../web/translator/lexical.mjs";

const expression = source => parse(`def result := ${source};`).declarations[0].value;
const refs = node => {
  const found = [];
  rewritten(node, n => {if (n.kind === "reference") found.push(n.binding); return n;});
  return found;
};

test("declaration identities survive every syntax transformation independently of spelling", () => {
  const env = new Map([["g", {tag: "DefRef", name: "module__g"}]]);
  const captured = capturedNames(expression("g(x)"), env);
  const identities = refs(captured);
  assert.equal(identities.length, 1);
  assert.deepEqual([...freeNames(captured)], ["x"]);
  for (const spelling of ["g", "x", "T", "__theory_type_0"]) {
    const renamed = renamedFree(captured, () => spelling);
    const inserted = substituted(expression(`fun (${spelling} : Unit) => hole`), new Map([["hole", renamed]]), assert.fail);
    assert.deepEqual(refs(inserted), identities);
    assert.ok(freeNames(inserted).has(spelling), "the inserted free variable must not become bound");
    assert.deepEqual(refs(relocated(inserted, {start: 100, end: 101, synthetic: true})), identities);
    assert.deepEqual(refs(JSON.parse(JSON.stringify(inserted))), identities);
  }
});

test("local and captured receivers have structural field selections", () => {
  const env = new Map([["T", {tag: "DefRef", name: "module__model"}]]);
  const local = capturedNames(expression("fun (T : Unit) => T.M"), env);
  assert.equal(local.body.kind, "member");
  assert.equal(local.body.value.name, "T");
  assert.equal(local.body.field.text, "M");
  assert.deepEqual(refs(local), []);
  const global = capturedNames(expression("T.parent.M"), env);
  assert.equal(global.kind, "member");
  assert.equal(global.value.kind, "member");
  assert.equal(global.value.value.kind, "reference");
  assert.deepEqual([...freeNames(global)], []);
});

test("lowering references for elaboration leaves the retained theory closure resolved", () => {
  const node = reference("\u0000binding module__f", "f", {start: 0, end: 1});
  const record = {fields: [{type: node}]};
  const lowered = elaborationSyntax({kind: "def", params: [], value: node, theory: record});
  assert.equal(lowered.value.kind, "name");
  assert.equal(lowered.value.name, node.binding);
  assert.equal(lowered.value.spelling, "f");
  assert.equal(lowered.theory, record);
  assert.equal(record.fields[0].type.kind, "reference");
});

test("a captured syntax closure is opaque to caller substitution and relocation", () => {
  const closure = {kind: "scoped", node: expression("x"), scope: {env: new Map([["x", "original"]])}, start: 0, end: 1};
  const result = substituted(closure, new Map([["x", expression("wrong")]]), assert.fail);
  assert.equal(result.node, closure.node);
  assert.equal(result.scope, closure.scope);
  assert.equal(relocated(closure, {start: 20, end: 21}).node, closure.node);
  assert.deepEqual([...freeNames(closure)], []);
});

test("parameter telescopes expose only earlier groups, and never their own shared domain", () => {
  const declaration = parse("def f(A, x : A, y : x) : Unit := tt;").declarations[0];
  assert.deepEqual([...freeNames(declaration)].sort(), ["A", "Unit", "tt"]);
  const captured = capturedNames(declaration, new Map([["A", {tag: "DefRef", name: "module__A"}]]));
  assert.equal(captured.params[0].type.kind, "reference");
  assert.equal(captured.params[1].type.kind, "reference");
  assert.equal(captured.params[2].type.kind, "name");
  assert.equal(captured.params[2].type.name, "x");
  const dependent = parse("def f(x : Unit, y : hole) : Unit := tt;").declarations[0];
  assert.throws(() => substituted(dependent, new Map([["hole", expression("x")]]), name => Error(`capture ${name}`)), /capture x/);
});

test("new syntax cannot silently opt out of scope checking", () => {
  assert.throws(() => freeNames({kind: "unregisteredBinder", body: expression("x")}), /Unregistered syntax kind/);
});

test("substitution is a no-op when its target is bound, including telescopes and overlapping scopes", () => {
  const declarations = [
    parse("def f(y : Unit, x : Unit) : Unit := y;").declarations[0],
    expression("fun (y, x : Unit) => y"),
    expression("induction n as y return Unit { zero => tt; succ x => y; }"),
  ];
  for (const node of declarations)
    assert.deepEqual(substituted(node, new Map([["y", expression("x")]]), assert.fail), node);
});

test("sequential statement binders cannot capture an inserted free variable", () => {
  for (const statement of ["let x := tt;", "obtain (x, z) := pair;", "intro x;", "ext x;", "simp only [] at h as x;"]) {
    const node = parse(`def f : Unit { ${statement} exact hole; }`).declarations[0];
    assert.ok(fixedBinders(node).has("x"), statement);
    assert.throws(() => substituted(node, new Map([["hole", expression("x")]]), name => Error(`capture ${name}`)), /capture x/, statement);
    assert.deepEqual(substituted(node, new Map([["x", expression("hole")]]), assert.fail), node);
  }
});

test("a statement scopes only its continuation, including substitutions into initializers", () => {
  const node = parse("def f : Unit { let x := hole; exact x; }").declarations[0];
  const result = substituted(node, new Map([["hole", expression("x")]]), assert.fail);
  assert.ok(freeNames(result).has("x"));
  assert.equal(result.body[0].value.name, "x");
  const shadowed = parse("def f : Unit { let hole := tt; let x := tt; exact hole; }").declarations[0];
  assert.deepEqual(substituted(shadowed, new Map([["hole", expression("x")]]), assert.fail), shadowed);
});
