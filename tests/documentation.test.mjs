import test from "node:test";
import assert from "node:assert/strict";
import { parse } from "../web/mathscript/parser.mjs";
import { leadingDocumentation } from "../web/mathscript/documentation.mjs";
import createCubical from "../web/dist/cubical.mjs";
import { CubicalProgram } from "../web/cubical-program.mjs";
test("declaration comments distinguish adjacent prose, paragraphs, headers and trailing comments", () => {
  const source = `// A section header.

// First paragraph wraps
// across two lines.
//
// Second paragraph: <b>plain text</b>.
def documented := 0;
// Detached comment.

def detached := 0; // Trailing comment belongs to this line.
def next := 0;
// Proof documentation.
def proof : Nat { exact 0; }
`;
  for (const newline of ["\n", "\r\n"]) {
    const text = source.replaceAll("\n", newline);
    const docs = Object.fromEntries(parse(text).declarations.map(d =>
      [d.name.text, leadingDocumentation(text, d.start)?.text ?? ""]));
    assert.deepEqual(docs, {
      documented: "First paragraph wraps across two lines.\n\nSecond paragraph: <b>plain text</b>.",
      detached: "", next: "", proof: "Proof documentation.",
    });
  }
  const inline = "// Header\ndef first := 0; def second := 0;";
  assert.equal(leadingDocumentation(inline, inline.indexOf("def second")), null);
});


test("documentation is extracted from checked local and imported source", async t => {
  const program = new CubicalProgram(await createCubical(), async () => "// Imported identity.\ndef identity(n : Nat) := n;");
  t.after(() => program.dispose());
  const result = await program.check("import helper;\n// Local definition.\ndef value := identity(0);", "docs");
  assert.equal(result.complete, true);
  assert.equal(result.outputs[0].description, "Local definition.");
  assert.equal(result.imports.find(x => x.name === "identity").description, "Imported identity.");
});
