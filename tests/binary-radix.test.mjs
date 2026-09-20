import test, { after } from "node:test";
import assert from "node:assert/strict";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { parse, tokenize } from "../web/mathscript/parser.mjs";
import { binaryLiteralExpansion } from "../web/mathscript/binary-literals.mjs";
import { formatMathScript } from "../web/mathscript/formatter.mjs";
import { loadProof } from "../tools/test-selection.mjs";

const module = await createKernel();
const binary = await loadProof("web/proofs/binary_arithmetic.proof");
const radix = await loadProof("web/proofs/radix_factorial.proof");
const b = compile(module, binary.source, binary.sources);
const r = compile(module, radix.source, radix.sources);
after(() => { b.kernel.dispose(); r.kernel.dispose(); });

test("binary literals retain exact digits and expose their constructor macro", () => {
  const text = "0b1" + "0".repeat(60) + "1";
  const n = parse(text, true);
  assert.equal(n.digits, text.slice(2));
  assert.equal(tokenize(text)[0].text, text);
  assert.equal(parse("0b0000", true).digits, "0");
  assert.equal(binaryLiteralExpansion(parse("0b110", true)), "binary_positive(binary_bit0(binary_bit1(binary_one)))");
  const link = b.links.find(l => l.role === "binary-number literal" && l.name === "0b1101110101111100000000");
  assert.ok(link);
  assert.match(link.expansion, /^binary_positive\(/);
  assert.equal(link.type, "BinaryNat");
  const source = `import binary_naturals; def exact_digits = ${text};`;
  assert.match(formatMathScript(source), new RegExp(text));
  const c = compile(module, source, binary.sources);
  try { assert.equal(c.axiomCount, 0); } finally { c.kernel.dispose(); }
});

test("malformed binary literals are rejected instead of being split into names", () => {
  for (const spelling of ["0b", "0b2", "0b102", "0b10foo", "0b1_0"])
    assert.throws(() => parse(spelling, true), /Unexpected character/);
  assert.throws(() => parse("0b1".padEnd(260, "0"), true), /256 significant bits/);
  assert.throws(() => compile(module, "def n = 0b1;"), /import binary_naturals/);
  assert.throws(() => compile(module,
    "import binary_naturals; theorem wrong_carrier : 0b1 =[Nat] 1 { exact refl(1); }",
    binary.sources), /Expected|differ/);
});

test("the kernel checks binary 10! and both generic radix instances without axioms", () => {
  for (const [c, names] of [[b, ["binary_factorial_ten"]],
    [r, ["radix_factorial_ten_base_two", "radix_factorial_ten_base_ten"]]]) {
    for (const name of names) {
      assert.ok(c.kernel.verify(name + "_type", name));
      assert.deepEqual(c.kernel.axiomsFor(name), []);
    }
    // This is a manual W-arithmetic regression, not yet the cubical Nat test.
    assert.ok(c.kernel.stats().nodes < 500000);
    assert.ok(c.kernel.stats().bytes < 100 * 1024 * 1024);
  }
  assert.equal(BigInt("0b1101110101111100000000"), 3628800n);
});

test("a wrong factorial endpoint is rejected", () => {
  assert.throws(() => compile(module, binary.source.replace(
    "binary_factorial(3) = 0b110",
    "binary_factorial(3) = 0b111"), binary.sources), /Expected|differ/);
});

test("W introduction rejects a child function with the wrong arity", () => {
  assert.throws(() => compile(module, `
    def Tree = W(Unit, fun (tag : Unit) => Void);
    def invalid = sup(Tree, tt, fun (child : Unit) => tt);
  `), /Expected|differ/);
});

test("W induction rejects a branch missing its recursive hypotheses", () => {
  assert.throws(() => compile(module, `
    def Tree = W(Unit, fun (tag : Unit) => Void);
    def leaf = sup(Tree, tt, fun (v : Void) => typed(Tree, absurd(v)));
    def invalid = wrec(Tree, fun (tree : Tree) => Nat,
      fun (tag : Unit) => fun (children : Void -> Tree) => 0, leaf);
  `), /Expected|differ/);
});

test("general dependent W induction computes and enforces its result family", () => {
  const source = `
    def Tree = W(Unit, fun (tag : Unit) => Void);
    def leaf = sup(Tree, tt, fun (v : Void) => typed(Tree, absurd(v)));
    def identity_tree(t : Tree) = wrec(Tree, fun (tree : Tree) => tree = tree,
      fun (tag : Unit) => fun (children : Void -> Tree) =>
      fun (ih : forall v : Void, children(v) = children(v)) => refl(sup(Tree, tag, children)), t);
    theorem computes : identity_tree(leaf) = refl(leaf) { exact refl(refl(leaf)); }
  `;
  const c = compile(module, source);
  try { assert.ok(c.kernel.verify("computes_type", "computes")); }
  finally { c.kernel.dispose(); }
  assert.throws(() => compile(module, source.replace("=> refl(sup(Tree, tag, children))", "=> refl(0)")), /Expected|differ/);
});
