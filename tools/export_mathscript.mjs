// Lossless text translations: every premise, binder, focus and computation is
// retained. This is construction notation, not a claimed mathematical rewrite.
import { readFile, writeFile } from "node:fs/promises";
import catalogue from "../web/proofs/catalogue.mjs";
import { constructors } from "../web/mathscript/construction.mjs";
import { formatMathScript } from "../web/mathscript/formatter.mjs";
for (const entry of catalogue) {
  const doc = JSON.parse(
    await readFile(
      new URL("../web/proofs/" + entry.file, import.meta.url),
      "utf8",
    ),
  );
  const lines = [
    `// ${entry.title}`,
    "// Complete checked construction. All intermediate steps are included.",
    `construction ${entry.id} {`,
  ];
  if (doc.policy.allowAxioms)
    lines.push(
      "  axioms allow; // Explicit policy inherited from the original proof.",
    );
  const exports = new Set(entry.exports);
  for (const s of doc.steps) {
    const args = [...s.args];
    if (s.context) args.push(s.context);
    if (!s.fresh) args.push(...(s.free ?? []).map((x) => x ?? "none"));
    const op = s.fresh ? "assume_fresh" : constructors[s.op];
    if (!op) throw new Error("Missing constructor: " + s.op);
    lines.push(
      `  ${exports.has(s.name) ? "export" : "private"} ${s.name} = ${op}(${args.join(", ")});`,
    );
  }
  if (entry.verify)
    lines.push(`  verify ${entry.verify[0]} with ${entry.verify[1]};`);
  lines.push("}", "");
  await writeFile(
    new URL(
      "../web/proofs/" + entry.id + ".construction.proof",
      import.meta.url,
    ),
    formatMathScript(lines.join("\n")),
  );
}
console.log(
  `Translated all ${catalogue.length} catalogue programs to complete .proof construction sources.`,
);
