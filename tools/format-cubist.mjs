import { readFile, writeFile } from "node:fs/promises";
import { resolve } from "node:path";
import { formatCubist } from "../web/cubist/formatter.mjs";
import { cubistSources } from "./cubist-sources.mjs";

const args = process.argv.slice(2), check = args.includes("--check");
if (args.includes("--help")) {
  console.log("Usage: npm run format:cubist -- [--check] [file.cubist ...]\nWith no files, format every .cubist source git tracks, including AST-checked tuple linearization. --check reports changes without writing.");
} else {
  const files = args.filter(a => a !== "--check");
  if (files.some(a => a.startsWith("--"))) throw new Error("Unknown formatter option.");
  if (!files.length) files.push(...cubistSources());
  let changed = 0;
  for (const file of files) {
    const path = file instanceof URL ? file : resolve(file);
    const source = await readFile(path, "utf8"), formatted = formatCubist(source);
    if (source === formatted) continue;
    changed++;
    if (!check) await writeFile(path, formatted);
    else console.log(String(file));
  }
  console.log(`${files.length} sources checked; ${changed} ${check ? "need formatting" : "formatted"}.`);
  if (check && changed) process.exitCode = 1;
}
