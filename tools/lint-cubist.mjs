import { readFile, readdir } from "node:fs/promises";
import { relative, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { lint } from "../web/mathscript/lint.mjs";

// Reports bindings that are never used and can be removed
// (web/mathscript/lint.mjs). Exits with status 1 when there are any.
const args = process.argv.slice(2);
if (args.includes("--help")) {
  console.log("Usage: npm run lint:cubist -- [file.cubist ...]\nWith no files, lint every library/*.cubist module. Reports unused `as` names, quantified variables, let, have and obtain bindings that can be removed.");
} else {
  if (args.some(a => a.startsWith("--"))) throw new Error("Unknown lint option.");
  const library = fileURLToPath(new URL("../library/", import.meta.url));
  const files = args.length ? args.map(file => resolve(file))
    : (await readdir(library)).filter(n => n.endsWith(".cubist")).sort().map(n => resolve(library, n));
  let count = 0;
  for (const path of files)
    for (const warning of lint(await readFile(path, "utf8"))) {
      count++;
      console.log(`${relative(process.cwd(), path)}:${warning.line}:${warning.column}: ${warning.message}`);
    }
  console.log(`${files.length} sources linted; ${count} warning${count === 1 ? "" : "s"}.`);
  if (count) process.exitCode = 1;
}
