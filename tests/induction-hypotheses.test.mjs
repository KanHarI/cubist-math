import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { parse } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { freeNames, substituted } from "../web/cubist/scopes.mjs";
import { checkProgram } from "./check-program.mjs";
import { verifyMigration } from "../tools/proof-migration.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { checkedHypothesisStarts, migrateInductionHypotheses } from "../tools/induction-migration.mjs";

const declarations = `import nat; use nat;
inductive Tree { leaf; node(l : Tree, datum : Nat, r : Tree); }
inductive Forest { empty; grow(children : Nat -> Forest); }
inductive EmptyTree { tip; sprout(children : Void -> EmptyTree); }
inductive Loopy { base; loop(x : Loopy) : x = x; }
`;
const examples = `
computable def size(t : Tree) : Nat := induction t return Nat {
  leaf => 0; node(l, datum, r) with ih_l, ih_r => datum + ih_l + ih_r;
};
computable def erase(t : Tree) : Unit { induction t {
  leaf => { exact tt; } node(l, datum, r) with ih_l, ih_r => { exact ih_r; }
} }
computable def omit(t : Tree) : Nat := induction t return Nat { leaf => 0; node(l, datum, r) => datum; };
computable def depth(t : Forest) : Nat := induction t return Nat { empty => 0; grow(children) with below => succ(below(0)); };
computable def vacuous(t : EmptyTree) : Void -> Unit := induction t return (Void -> Unit) {
  tip => fun (v : Void) => absurd(v);
  sprout(children) with ih => fun (v : Void) => ih(v)(v);
};
computable def loops(t : Loopy) : Unit := induction t return Unit { base => tt; loop(x) @ i with ih => ih; };
computable def loop_blocks(t : Loopy) : Unit { induction t {
  base => { exact tt; } loop(x) @ i with ih => { exact ih; }
} }
computable def loop_obligations(t : Loopy) : Unit { induction t {
  base => { exact tt; }
} obligations { loop(x) @ i with ih => { exact ih; } } }
computable def copy(t : Tree) : Tree := induction t return Tree {
  leaf => leaf; node(l, datum, r) with ih_l, ih_r => node(ih_l, datum, ih_r);
};
computable def doubled(n : Nat) : Nat := induction n return Nat { zero => 0; succ(k) with h => succ(succ(h)); };
computable def specialized(n : Nat) : Nat := induction n return Nat { zero => 0; succ h => succ(succ(h)); };
def agrees : doubled = specialized { rfl; }
evaluate(size(node(node(leaf, 2, leaf), 3, node(leaf, 4, leaf)))) expecting 9;
evaluate(depth(grow(fun (n : Nat) => empty))) expecting 1;
evaluate(doubled(3)) expecting 6;
`;

test("separate hypotheses check and compute for data, functions, paths and proof blocks", async t => {
  const source = formatCubist(declarations + examples);
  const { result, program } = await checkProgram(t, source);
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  assert.equal(formatCubist(source), source);
  const clause = parse(source).declarations.find(d => d.name.text === "size").body[0].value.clauses[1];
  assert.equal(clause.args.length, 3);
  assert.deepEqual(clause.hypotheses.map(h => h.text), ["ih_l", "ih_r"]);
  for (const token of clause.hypotheses) {
    assert.equal(source.slice(token.start, token.end), token.text);
    const link = result.links.find(link => link.start === token.start);
    assert.equal(link.role, "induction hypothesis");
    assert.match(program.inspect(link.binding).typeText, /Nat/);
    assert.ok(result.links.some(link => link.start > token.end && link.definitionStart === token.start));
  }
});

test("old and new clause spellings have identical checked terms, types and assumptions", async () => {
  const original = (declarations + examples).replace(/\) with ([\w, ]+) =>/g, ", $1) =>")
    .replace(/loop\(x\) @ i with ih/g, "loop(x, ih) @ i");
  const reader = sourceReader();
  const [report] = await verifyMigration({ modules: ["fixture"], level: "identical",
    readOriginal: name => name === "fixture" ? original : reader(name),
    readEdited: name => name === "fixture" ? declarations + examples : reader(name) });
  assert.deepEqual(report.failures, []);
  assert.ok(report.identical >= 10);
});

test("hypotheses bind only in their clause body and substitutions avoid capture", () => {
  const value = parse("induction t return P { leaf => ih; node(l, datum, r) with ih, other => f(ih, other, outer); }", true);
  assert.deepEqual([...freeNames(value)].sort(), ["P", "f", "ih", "outer", "t"]);
  const result = substituted(value, new Map([["outer", { kind: "name", name: "other" }]]), name => Error(name));
  assert.notEqual(result.clauses[1].hypotheses[1].text, "other");
  assert.ok(freeNames(result).has("other"));
});

test("with needs a nonempty list, follows coordinates, and is forbidden on match", () => {
  for (const text of [
    "induction t { node(l, d, r) with => 0; }",
    "induction t { node(l, d, r) with h, => 0; }",
    "induction t { loop(x) with h @ i => h; }",
    "induction t { node(l, d, r), extra with h, j => 0; }",
    "match t { node(l, d, r) with h, j => 0; }",
  ]) assert.throws(() => parse(text, true));
  assert.throws(() => parse("def bad(t : Tree) : Unit { match t { node(l, d, r) with h, j => { exact tt; } } }"), /only available in induction/);
});

test("wrong counts and mixed spellings fail, while body unfolding and shadowing work", async t => {
  const { get } = await checkProgram(t, declarations + `
def few(t : Tree) : Nat := induction t return Nat { leaf => 0; node(l, d, r) with h => 0; };
def many(t : Tree) : Nat := induction t return Nat { leaf => 0; node(l, d, r) with h, j, k => 0; };
def no_recursive(t : Tree) : Nat := induction t return Nat { leaf with h => 0; node(l, d, r) => 0; };
def mixed(t : Tree) : Nat := induction t return Nat { leaf => 0; node(l, d, r, h, j) with k, m => 0; };
def fields(t : Tree) : Nat := induction t return Nat { leaf => 0; node(l, r) with h, j => 0; };
def escapes(t : Tree) : Nat := induction t return Nat { leaf => ih; node(l, d, r) with ih, other => ih; };
def construction : Tree := node(leaf, 0, leaf, 1, 2);
def identity(n : Nat) : Nat := n;
def unfolded(t : Tree) : Nat := induction t return Nat { leaf => 0; node(l, d, r) with h, j => with unfolding [identity] { identity(h) }; };
def shadow(t : Tree) : Nat := induction t return Nat { leaf => 0; node(l, d, r) with t, j => t; };
`);
  for (const name of ["few", "many", "no_recursive"]) assert.match(get(name).reason, /supplies .* induction hypotheses/);
  assert.match(get("mixed").reason, /Keep only.*constructor fields/);
  assert.match(get("fields").reason, /constructor fields in parentheses/);
  for (const name of ["escapes", "construction"]) assert.equal(get(name).verified, false, name);
  for (const name of ["unfolded", "shadow"]) assert.equal(get(name).verified, true, get(name).reason);
});

test("checked migration preserves nested clauses, coordinates and comments", async t => {
  const original = declarations + `
// A constructor of another type has the same spelling and another arity.
inductive Other { stop; node(datum : Nat); }
def plain(t : Tree) : Nat := match t { leaf => 0; node(l, d, r) => d; };
def nested(t : Tree) : Nat := induction t return Nat {
  leaf => 0;
  node(l, datum, r, // left hypothesis
    ih_l, // right hypothesis
    ih_r // before close
  ) => induction l return Nat { leaf => ih_r; node(a, d, b, h, j) => h; };
};
def along_loop(t : Loopy) : Unit := induction t return Unit { base => tt; loop(x, // hypothesis
  ih) // coordinate
  @ i => ih; };
def blocks(t : Tree) : Unit { induction t { leaf => { exact tt; } node(l, d, r, h, j) => { exact j; } } }
`;
  const { program, result } = await checkProgram(t, original, { name: "fixture" });
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  const migrated = migrateInductionHypotheses(original, checkedHypothesisStarts(program, "fixture"));
  assert.equal(migrated.clauses, 4);
  assert.deepEqual(migrated.source.match(/\/\/[^\n]*/g)?.sort(), original.match(/\/\/[^\n]*/g)?.sort());
  assert.match(migrated.source, /@ i with/);
  const edited = formatCubist(migrated.source);
  const reader = sourceReader();
  const [report] = await verifyMigration({ modules: ["fixture"], level: "identical",
    readOriginal: name => name === "fixture" ? original : reader(name),
    readEdited: name => name === "fixture" ? edited : reader(name) });
  assert.deepEqual(report.failures, []);
  assert.equal(migrateInductionHypotheses(edited, new Set()).source, edited);
});

test("printed induction preserves source field order and emits with", async t => {
  for (const name of ["size", "copy"]) {
    const { result } = await checkProgram(t, declarations + examples + `print(evaluate(${name}));`);
    const printed = result.prints[0].text;
    assert.match(printed, /node\(l, datum, r\) with \w+, \w+/);
    const { result: readback } = await checkProgram(t, declarations + examples + `def again := ${printed}; def same : ${name} = again { rfl; }`);
    assert.equal(readback.complete, true, JSON.stringify(readback.gaps));
  }
});
