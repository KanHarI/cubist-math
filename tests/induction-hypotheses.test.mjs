import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { parse } from "../web/cubist/parser.mjs";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { freeNames } from "../web/cubist/scopes.mjs";
import { checkProgram } from "./check-program.mjs";
import { verifyMigration } from "../tools/proof-migration.mjs";
import { sourceReader } from "../tools/module-sources.mjs";
import { checkedHypothesisStarts, migrateInductionHypotheses } from "../tools/induction-migration.mjs";

const declarations = `import unat; use unat;
inductive Tree { leaf; node(l : Tree, datum : UNat, r : Tree); }
inductive Forest { empty_forest; grow(children : UNat -> Forest); }
inductive EmptyTree { tip; sprout(children : Void -> EmptyTree); }
inductive Loopy { base; loop(x : Loopy) : x = x; }
`;
const examples = `
computable def size(t : Tree) : UNat := induction t return UNat {
  leaf => 0; node(l, datum, r) with ih_l, ih_r => datum + ih_l + ih_r;
};
computable def erase(t : Tree) : Unit { induction t {
  leaf => { exact tt; } node(l, datum, r) with ih_l, ih_r => { exact ih_r; }
} }
computable def omit(t : Tree) : UNat := induction t return UNat { leaf => 0; node(l, datum, r) => datum; };
computable def depth(t : Forest) : UNat := induction t return UNat { empty_forest => 0; grow(children) with below => succ(below(0)); };
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
computable def left_depth(t : Tree) : UNat := induction t return UNat {
  leaf => 0; node(l, datum, r) with ih_l, ih_r => succ(ih_l);
};
computable def right_depth(t : Tree) : UNat { induction t {
  leaf => { exact 0; } node(l, datum, r) with ih_l, ih_r => { exact succ(ih_r); }
} }
computable def doubled(n : UNat) : UNat := induction n return UNat { zero => 0; succ(k) with h => succ(succ(h)); };
computable def specialized(n : UNat) : UNat := induction n return UNat { zero => 0; succ h => succ(succ(h)); };
def agrees : doubled = specialized { rfl; }
evaluate(size(node(node(leaf, 2, leaf), 3, node(leaf, 4, leaf)))) expecting 9;
evaluate(left_depth(node(node(leaf, 0, leaf), 0, leaf))) expecting 2;
evaluate(right_depth(node(node(leaf, 0, leaf), 0, leaf))) expecting 1;
evaluate(left_depth(copy(node(node(leaf, 0, leaf), 0, leaf)))) expecting 2;
evaluate(depth(grow(fun (n : UNat) => empty_forest))) expecting 1;
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
    assert.match(program.inspect(link.binding).typeText, /UNat/);
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

test("hypotheses bind only in their clause body", () => {
  const value = parse("induction t return P { leaf => ih; node(l, datum, r) with ih, other => f(ih, other, outer); }", true);
  assert.deepEqual([...freeNames(value)].sort(), ["P", "f", "ih", "outer", "t"]);
});

test("with needs a nonempty list, follows coordinates, and is forbidden on match", () => {
  for (const [text, message] of [
    ["induction t { node(l, d, r) with => 0; }", /Expected a name\./],
    ["induction t { node(l, d, r) with h, => 0; }", /Expected a name\./],
    ["induction t { loop(x) with h @ i => h; }", /Expected '=>', found '@'\./],
    ["induction t { node(l, d, r), extra with h, j => 0; }", /An induction clause takes one constructor pattern\./],
    ["match t { node(l, d, r) with h, j => 0; }", /Induction hypotheses after with are only available in induction clauses\./],
  ]) assert.throws(() => parse(text, true), message);
  assert.throws(() => parse("def bad(t : Tree) : Unit { match t { node(l, d, r) with h, j => { exact tt; } } }"), /only available in induction/);
});

test("wrong counts and mixed spellings fail, while body unfolding and shadowing work", async t => {
  const { get, result } = await checkProgram(t, declarations + `
def few(t : Tree) : UNat := induction t return UNat { leaf => 0; node(l, d, r) with h => 0; };
def many(t : Tree) : UNat := induction t return UNat { leaf => 0; node(l, d, r) with h, j, k => 0; };
def single(t : Forest) : UNat := induction t return UNat { empty_forest => 0; grow(children) with a, b => 0; };
def no_recursive(t : Tree) : UNat := induction t return UNat { leaf with h => 0; node(l, d, r) => 0; };
def arity(t : Tree) : UNat := match t { leaf => 0; node(l, d) => d; };
def nullary(t : Tree) : UNat := match t { leaf(x) => 0; node(l, d, r) => d; };
def mixed(t : Tree) : UNat := induction t return UNat { leaf => 0; node(l, d, r, h, j) with k, m => 0; };
def fields(t : Tree) : UNat := induction t return UNat { leaf => 0; node(l, r) with h, j => 0; };
def escapes(t : Tree) : UNat := induction t return UNat { leaf => ih; node(l, d, r) with ih, other => ih; };
def construction : Tree := node(leaf, 0, leaf, 1, 2);
def identity(n : UNat) : UNat := n;
def unfolded(t : Tree) : UNat := induction t return UNat { leaf => 0; node(l, d, r) with h, j => with unfolding [identity] { identity(h) }; };
def shadow(t : Tree) : UNat := induction t return UNat { leaf => 0; node(l, d, r) with t, j => t; };
`);
  for (const [name, code, message] of [
    ["few", "E578", /^node has 2 recursive fields, so with names 2 induction hypotheses, not 1; or omit with\./],
    ["many", "E578", /^node has 2 recursive fields, so with names 2 induction hypotheses, not 3; or omit with\./],
    ["single", "E578", /^grow has 1 recursive field, so with names 1 induction hypothesis, not 2; or omit with\./],
    ["no_recursive", "E579", /^leaf has no recursive fields, so it has no induction hypotheses: remove with\./],
    ["mixed", "E577", /^Keep only the 3 constructor fields of node in parentheses; name induction hypotheses after with\./],
    ["fields", "E557", /^node takes 3 constructor fields in parentheses; name its 2 induction hypotheses after with, or omit with\./],
    ["arity", "E538", /^node takes 3 arguments here, so its clause names all 3 in parentheses: node\(…\)\./],
    ["nullary", "E538", /^leaf takes 0 arguments here, so its clause writes leaf without parentheses\./],
  ]) {
    assert.match(get(name).reason, message);
    assert.equal(result.gaps.find(gap => gap.name === name)?.code, code, name);
  }
  for (const name of ["escapes", "construction"]) assert.equal(get(name).verified, false, name);
  for (const name of ["unfolded", "shadow"]) assert.equal(get(name).verified, true, get(name).reason);
});

test("checked migration preserves nested clauses, coordinates and comments", async t => {
  // The node in scope is another type's, of another arity. A module declares
  // each name once (E872), so the clauses' types are imported.
  const library = sourceReader();
  const reader = (name, importer) => name === "tree_types" ? declarations : library(name, importer);
  const original = "import tree_types; import unat; use unat;\ninductive Other { stop; node(datum : UNat); }\n" + `
def plain(t : Tree) : UNat := match t { leaf => 0; node(l, d, r) => d; };
def nested(t : Tree) : UNat := induction t return UNat {
  leaf => 0;
  node(l, datum, r, // left hypothesis
    ih_l, // right hypothesis
    ih_r // before close
  ) => induction l return UNat { leaf => ih_r; node(a, d, b, h, j) => h; };
};
def along_loop(t : Loopy) : Unit := induction t return Unit { base => tt; loop(x, // hypothesis
  ih) // coordinate
  @ i => ih; };
def blocks(t : Tree) : Unit { induction t { leaf => { exact tt; } node(l, d, r, h, j) => { exact j; } } }
// A directive's references are recorded with the declaration after it, and a
// last directive's not at all: neither is migrated, and both are reported.
evaluate(induction 2 return UNat { zero => 0; succ(k, h) => succ(h); }) expecting 2;
def after_directive : UNat := 0;
print(evaluate(induction 1 return UNat { zero => 0; succ(k, h) => h; }));
`;
  const { program, result } = await checkProgram(t, original, { name: "fixture", reader });
  assert.equal(result.complete, true, JSON.stringify(result.gaps));
  const migrated = migrateInductionHypotheses(original, checkedHypothesisStarts(program, "fixture"));
  assert.equal(migrated.clauses, 4);
  assert.deepEqual(migrated.unchecked, ["succ(k, h) => succ(h)", "succ(k, h) => h"].map(text => original.indexOf(text)));
  for (const text of ["succ(k, h) => succ(h)", "succ(k, h) => h"]) assert.ok(migrated.source.includes(text), text);
  assert.deepEqual(migrated.source.match(/\/\/[^\n]*/g)?.sort(), original.match(/\/\/[^\n]*/g)?.sort());
  assert.match(migrated.source, /@ i with/);
  const edited = formatCubist(migrated.source);
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
