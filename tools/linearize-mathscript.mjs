import { readFile, writeFile, readdir } from "node:fs/promises";
import { resolve } from "node:path";
import { linearizeTuples } from "../web/mathscript/tuples.mjs";
import { formatMathScript } from "../web/mathscript/formatter.mjs";

const args = process.argv.slice(2), check = args.includes("--check");
if (args.includes("--help")) {
  console.log("Usage: npm run linearize:mathscript -- [--check] [file.proof ...]\nWith no files, scan every web/proofs/*.proof source. Flatten right-nested pairs and obtain patterns; preserve comments and expanded ASTs. Construction sources are skipped. --check reports changes without writing.");
} else {
  const files = args.filter(a => a !== "--check");
  if (files.some(a => a.startsWith("--"))) throw new Error("Unknown tuple linearization option.");
  if (!files.length) files.push(...(await readdir(new URL("../web/proofs/", import.meta.url)))
    .filter(n => n.endsWith(".proof")).sort().map(n => new URL("../web/proofs/" + n, import.meta.url)));
  // Validate every rewrite before writing any of the selected sources.
  const changes = [];
  for (const file of files) {
    const path = file instanceof URL ? file : resolve(file);
    const result = linearizeTuples(await readFile(path, "utf8"));
    if (result.count) changes.push({ path, ...result, source: formatMathScript(result.source) });
  }
  for (const change of changes) {
    if (check) console.log(`${String(change.path)}: ${change.count} nested pairs`);
    else await writeFile(change.path, change.source);
  }
  console.log(`${files.length} sources scanned; ${changes.reduce((n, c) => n + c.count, 0)} nested pairs ${check ? "can be linearized" : "linearized"} in ${changes.length} files.`);
  if (check && changes.length) process.exitCode = 1;
}
