import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import { parse, tokenize } from "../web/mathscript/parser.mjs";
import { formatMathScript } from "../web/mathscript/formatter.mjs";
import { expandedSyntax } from "../web/mathscript/tuples.mjs";

const expression = text => parse(text, true);

test("unfolding scopes separate definition names from the body expression", () => {
  const source = "with unfolding [identity, wrapper] { refl(0) }";
  const node = expression(source);
  assert.equal(node.kind, "withUnfolding");
  assert.deepEqual(node.hints.map(n => n.text), ["identity", "wrapper"]);
  assert.equal(node.body.kind, "call");
  assert.equal(node.body.fn.name, "refl");
  assert.equal(source.slice(node.start, node.end), source);
  for (const hint of node.hints) assert.equal(source.slice(hint.start, hint.end), hint.text);
  assert.equal(expression("with unfolding [] { 0 }").hints.length, 0);
});

test("scopes nest and compose as ordinary expressions", () => {
  const node = expression("with unfolding [f] { with unfolding [g] { f } }(0)");
  assert.equal(node.kind, "call");
  assert.equal(node.fn.kind, "withUnfolding");
  assert.equal(node.fn.body.kind, "withUnfolding");
  const sum = expression("with unfolding [f] { f(0) } + 1");
  assert.equal(sum.kind, "binary");
  assert.equal(sum.left.kind, "withUnfolding");
});

test("hint lists accept names only and braces contain exactly one expression", () => {
  for (const invalid of [
    "with unfolding [f(0)] { refl(0) }",
    "with unfolding [0] { refl(0) }",
    "with unfolding [f,] { refl(0) }",
    "with unfolding [f] { refl(0); }",
    "with unfolding [f] { exact refl(0); }",
    "with unfolding [f] {}",
    "with unfolding f { refl(0) }",
  ]) assert.throws(() => expression(invalid), invalid);
});

test("formatting preserves scoped blocks, comments, postfix calls and tuples", () => {
  const source = `def result = with unfolding [identity, wrapper] {
// A scoped strategy.
with unfolding [inner] { (identity, (wrapper, inner)) }
};
def application = with unfolding [identity] { identity }(0);
def sum = with unfolding [] { 0 } + 1;`;
  for (const printWidth of [40, 80, 100]) {
    const formatted = formatMathScript(source, { printWidth });
    assert.equal(expandedSyntax(parse(formatted)), expandedSyntax(parse(source)));
    assert.equal(formatMathScript(formatted, { printWidth }), formatted);
    assert.match(formatted, /with unfolding \[identity\] \{\n\s+identity\n\s*\}\(0\)/);
    assert.match(formatted, /\/\/ A scoped strategy\./);
    assert.deepEqual(tokenize(formatted).filter(t => ["with", "unfolding"].includes(t.text)).map(t => t.text),
      ["with", "unfolding", "with", "unfolding", "with", "unfolding", "with", "unfolding"]);
  }
});

test("both language references and keyword styling describe the scoped syntax", async () => {
  for (const file of ["proof.html", "language.html"]) {
    const text = await readFile(new URL(`../web/${file}`, import.meta.url), "utf8");
    assert.match(text, /with unfolding \[/);
    assert.doesNotMatch(text, /with_unfolding\(/);
  }
  const viewer = await readFile(new URL("../web/proof.mjs", import.meta.url), "utf8");
  const keywords = viewer.slice(viewer.indexOf("const keywords ="), viewer.indexOf("const builtinForms ="));
  assert.match(keywords, /"with"/);
  assert.match(keywords, /"unfolding"/);
});

test("migrated native proof scopes format without changing their expanded syntax", async () => {
  for (const name of ["binomial_pascal", "embedded_composita", "f4_embedded_composita",
    "f4_embedding_images", "group_univalence", "kernel_quotient_image", "permutations", "structured_sets"]) {
    const source = await readFile(new URL(`../web/proofs/${name}.cubist`, import.meta.url), "utf8");
    assert.doesNotMatch(source, /with_unfolding\(/, name);
    const formatted = formatMathScript(source);
    assert.equal(expandedSyntax(parse(formatted)), expandedSyntax(parse(source)), name);
    assert.equal(formatMathScript(formatted), formatted, name);
  }
});
