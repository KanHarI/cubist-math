// Where the syntax binds names (web/cubist/scopes.mjs), which every
// substitution, renaming and free-name traversal reads. A binding form the
// table does not describe is one a substitution captures through: a
// notation rule's induction hypothesis was once taken for its operand, and a
// derived operation's for its argument. So every kind of node the parser and
// the theory expansion build must be described, binding or not, and each
// binding form is checked here.
import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import { parse } from "../web/cubist/parser.mjs";
import { BINDING, UNBINDING, freeNames, substituted } from "../web/cubist/scopes.mjs";

const root = fileURLToPath(new URL("../", import.meta.url));
const described = kind => BINDING.has(kind) || UNBINDING.has(kind);

test("every kind of node the parser and the theory expansion write is described", () => {
  for (const file of ["web/cubist/parser.mjs", "web/cubist/theories.mjs", "web/cubist/morphisms.mjs", "web/cubist/tuples.mjs"])
    for (const [, kind] of readFileSync(root + file, "utf8").matchAll(/kind: *"([A-Za-z_]+)"/g))
      assert.ok(described(kind), `${kind} (${file}) is in scopes.mjs, as binding or not`);
});

test("every kind of node in the repository's sources is described", () => {
  const kinds = new Set();
  const visit = (node, seen) => {
    if (!node || typeof node !== "object" || seen.has(node)) return;
    seen.add(node);
    if (node.kind) kinds.add(node.kind);
    // Hidden fields too: an induction keeps its clauses beside its step.
    for (const key of Object.getOwnPropertyNames(node)) visit(node[key], seen);
  };
  const files = execFileSync("git", ["ls-files", "-z", "--", "*.cubist"], { cwd: root, encoding: "utf8" }).split("\0").filter(Boolean);
  for (const file of files) {
    let syntax;
    try { syntax = parse(readFileSync(root + file, "utf8")); } catch { continue; }
    visit(syntax, new Set());
  }
  assert.ok(kinds.size > 40);
  for (const kind of kinds) assert.ok(described(kind), `${kind} is in scopes.mjs, as binding or not`);
});

// An expression's syntax: the value of def t := e;.
const expression = source => {
  const declaration = parse(`def t := ${source};`).declarations[0];
  return declaration.body?.[0]?.value ?? declaration.value;
};
const free = source => [...freeNames(expression(source))].sort();

test("each binding form binds its names where it says", () => {
  const cases = [
    ["fun (x : A) => f(x, y)", ["A", "f", "y"]],
    ["fun (x, y : A) => g(x, y, z)", ["A", "g", "z"]],
    ["forall x : A. P(x)", ["A", "P"]],
    ["exists x : A. P(x, w)", ["A", "P", "w"]],
    ["path i => p @ i", ["p"]],
    // An induction's index in its motive, its hypothesis in its step.
    ["induction n as k return P(k) { zero => b; succ h => s(h, k); }", ["P", "b", "k", "n", "s"]],
    ["induction n return P { zero => b; succ x => x; }", ["P", "b", "n"]],
    // A sum's sides, and clauses with patterns and coordinates.
    ["match v as k return T(k) { left x => f(x); right y => g(y, k); }", ["T", "f", "g", "k", "v"]],
    ["match n { zero => a; succ(m) => b(m); }", ["a", "b", "n"]],
    ["match c { base => e; loop @ i => q @ i; }", ["c", "e", "q"]],
    ["unpack v as (l, r) return T { f(l, r); }", ["T", "f", "v"]],
  ];
  for (const [source, names] of cases) assert.deepEqual(free(source), names, source);
});

test("a block's statements bind names for the statements after them", () => {
  const declaration = parse("def t : T { let x : A := a; obtain (p, q) := r; intro h; exact f(x, p, q, h, y); }").declarations[0];
  assert.deepEqual([...freeNames(declaration.body)].sort(), ["A", "a", "f", "r", "y"]);
});

test("substitution renames a binder that would capture an argument's name, in every renamable form", () => {
  const argument = new Map([["y", { kind: "name", name: "x" }]]);
  const refuse = name => Object.assign(new Error(`refused ${name}`), { refused: name });
  for (const source of ["fun (x : A) => f(x, y)", "fun (x, z : A) => f(x, y)", "forall x : A. P(x, y)", "path x => p(y) @ x",
    "induction n return P { zero => y; succ x => f(x, y); }", "induction n as x return P(x, y) { zero => b; succ h => h; }",
    "match v return T { left x => f(x, y); right w => y; }", "unpack v as (x, r) return T { f(x, r, y); }",
    "match c { base => e; loop @ x => f(x, y); }"]) {
    const result = substituted(expression(source), argument, refuse);
    // The argument's x stays free, and none of the term's own x's is.
    assert.ok(freeNames(result).has("x"), source);
    assert.deepEqual([...freeNames(result)].filter(name => name === "y"), [], source);
  }
  // A pattern's argument may be a constructor: it is refused, never renamed.
  assert.throws(() => substituted(expression("match n { zero => y; succ(x) => f(x, y); }"), argument, refuse), /refused x/);
});
