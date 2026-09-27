import { readFile, writeFile, readdir } from "node:fs/promises";
import { resolve } from "node:path";
import { formatMathScript } from "../web/mathscript/formatter.mjs";

const args = process.argv.slice(2), check = args.includes("--check");
if (args.includes("--help")) {
  console.log("Usage: npm run format:mathscript -- [--check] [file.cubist ...]\nWith no files, format every archive/first-library/*.cubist source, including AST-checked tuple linearization. --check reports changes without writing.");
} else {
  const files = args.filter(a => a !== "--check");
  if (files.some(a => a.startsWith("--"))) throw new Error("Unknown formatter option.");
  if (!files.length) files.push(...(await readdir(new URL("../archive/first-library/", import.meta.url))).filter(n => n.endsWith(".cubist")).sort().map(n => new URL("../archive/first-library/" + n, import.meta.url)));
  let changed = 0;
  for (const file of files) {
    const path = file instanceof URL ? file : resolve(file);
    const source = await readFile(path, "utf8"), formatted = formatMathScript(source);
    if (source === formatted) continue;
    changed++;
    if (!check) await writeFile(path, formatted);
    else console.log(String(file));
  }
  console.log(`${files.length} sources checked; ${changed} ${check ? "need formatting" : "formatted"}.`);
  if (check && changed) process.exitCode = 1;
}
