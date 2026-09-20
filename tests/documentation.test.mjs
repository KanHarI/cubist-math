import test from "node:test";
import assert from "node:assert/strict";
import { readFile } from "node:fs/promises";
import createKernel from "../web/dist/kernel.mjs";
import { compile } from "../web/mathscript/compiler.mjs";
import { parse } from "../web/mathscript/parser.mjs";
import { leadingDocumentation } from "../web/mathscript/documentation.mjs";
import { declarations as interfaces } from "../web/mathscript/library.mjs";
const module = await createKernel();

test("declaration comments distinguish adjacent prose, paragraphs, headers and trailing comments", () => {
  const source = `// A section header.

// First paragraph wraps
// across two lines.
//
// Second paragraph: <b>plain text</b>.
opaque def documented = 0;
// Detached comment.

def detached = 0; // Trailing comment belongs to this line.
def next = 0;
// Proof documentation.
theorem proof : Nat { exact 0; }
// Explicit assumption documentation.
axiom assumed : Nat;
`;
  for (const newline of ["\n", "\r\n"]) {
    const text = source.replaceAll("\n", newline);
    const docs = Object.fromEntries(parse(text).declarations.map(d =>
      [d.name.text, leadingDocumentation(text, d.start)?.text ?? ""]));
    assert.deepEqual(docs, {
      documented: "First paragraph wraps across two lines.\n\nSecond paragraph: <b>plain text</b>.",
      detached: "", next: "", proof: "Proof documentation.", assumed: "Explicit assumption documentation.",
    });
  }
  const inline = "// Header\ndef first = 0; def second = 0;";
  assert.equal(leadingDocumentation(inline, inline.indexOf("def second")), null);
});

test("local and imported documentation follows its checked source and changes no kernel instructions", () => {
  const dependency = "// Imported identity.\ndef identity(A : U0, x : A) = x;";
  const source = `import dependency;
// Local inferred definition.
def value = identity(Nat, 0);
// Local checked theorem.
theorem result : Nat { exact value; }
// Local axiom.
axiom assumption : Nat;
`;
  const c = compile(module, source, { dependency });
  const plain = compile(module, source.replace(/\/\/[^\n]*/g, ""), { dependency: dependency.replace(/\/\/[^\n]*/g, "") });
  try {
    assert.deepEqual(c.outputs.map(d => d.description), ["Local inferred definition.", "Local checked theorem.", "Local axiom."]);
    assert.equal(c.imports.find(d => d.name === "identity").description, "Imported identity.");
    assert.deepEqual(c.kernel.steps, plain.kernel.steps);
    assert.deepEqual(c.kernel.axiomsFor("result"), []);
  } finally { c.kernel.dispose(); plain.kernel.dispose(); }
});

test("construction declarations also extract their own source documentation", () => {
  const c = compile(module, `construction documented {
// The natural-number type.
export N = natural_type();
// An internal zero.
private z = zero();
}`);
  try {
    assert.equal(c.outputs[0].description, "The natural-number type.");
    assert.equal(c.declarations.find(d => d.name === "z").description, "An internal zero.");
  } finally { c.kernel.dispose(); }
});

test("all arithmetic interface prose lives above the declaration and survives imports", async () => {
  const primes = await readFile(new URL("../web/proofs/primes.proof", import.meta.url), "utf8");
  const ast = parse(primes);
  const c = compile(module, "import primes; theorem example : Nat { exact 0; }", { primes });
  try {
    for (const entry of interfaces) {
      assert.ok(!("description" in entry) && !("title" in entry));
      const decl = ast.declarations.find(d => d.name.text === entry.name);
      const comment = leadingDocumentation(primes, decl.start);
      assert.ok(comment?.text, entry.name);
      assert.equal(c.imports.find(d => d.name === entry.name).description, comment.text);
    }
    assert.match(c.imports.find(d => d.name === "prime_divisor_exists").description,
      /A least divisor of m greater than one is prime\. The returned i names p = 2\+i\./);
  } finally { c.kernel.dispose(); }
});
