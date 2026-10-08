import "./fresh-build.mjs";
import test from "node:test";
import assert from "node:assert/strict";
import { parse } from "../web/cubist/parser.mjs";
import { leadingDocumentation } from "../web/cubist/documentation.mjs";
import { checkTestModule } from "./check-program.mjs";
test("declaration comments distinguish adjacent prose, paragraphs, headers and trailing comments", () => {
  const source = `// A section header.

// First paragraph wraps
// across two lines.
//
// Second paragraph: <b>plain text</b>.
def documented := 0;
// Detached comment.

def detached := 0; // Trailing comment belongs to this line.
def next_ := 0;
// Proof documentation.
def proof : Nat { exact 0; }
`;
  for (const newline of ["\n", "\r\n"]) {
    const text = source.replaceAll("\n", newline);
    const docs = Object.fromEntries(parse(text).declarations.map(d =>
      [d.name.text, leadingDocumentation(text, d.start)?.text ?? ""]));
    assert.deepEqual(docs, {
      documented: "First paragraph wraps across two lines.\n\nSecond paragraph: <b>plain text</b>.",
      detached: "", next_: "", proof: "Proof documentation.",
    });
  }
  const inline = "// Header\ndef first := 0; def second := 0;";
  assert.equal(leadingDocumentation(inline, inline.indexOf("def second")), null);
});


test("documentation is extracted from checked local and imported source", async t => {
  const { result } = await checkTestModule(t, "documentation_use");
  assert.equal(result.outputs[0].description, "Local definition.");
  assert.equal(result.imports.find(x => x.name === "identity").description, "Imported identity.");
});
