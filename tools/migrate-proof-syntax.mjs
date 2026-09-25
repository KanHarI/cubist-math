// Rewrite library proofs to newer syntax, then format them.
//   node tools/migrate-proof-syntax.mjs --rewrites a,b [--skip FILE.json] [module ...]
// Without module names, every web/proofs module is rewritten in place. The
// skip file maps module names to declarations that must stay unchanged.
// Verify the result with tools/verify-proof-migration.mjs.
import { readFile, readdir, writeFile } from "node:fs/promises";
import { fileURLToPath } from "node:url";
import { formatMathScript } from "../web/mathscript/formatter.mjs";
import { identicalRewrites, typePreservingRewrites, rewriteModule } from "./proof-rewrites.mjs";

const root = fileURLToPath(new URL("../", import.meta.url));
const args = process.argv.slice(2), option = name => {
  const index = args.indexOf(name);
  if (index < 0) return undefined;
  const value = args[index + 1];
  args.splice(index, 2);
  return value;
};
const known = [...identicalRewrites, ...typePreservingRewrites];
const rewrites = (option("--rewrites") ?? identicalRewrites.join(",")).split(",").filter(Boolean);
for (const name of rewrites) if (!known.includes(name)) throw new Error(`Unknown rewrite ${name}; expected ${known.join(", ")}.`);
const skipFile = option("--skip");
const skips = skipFile ? JSON.parse(await readFile(skipFile, "utf8")) : {};
const modules = args.length ? args : (await readdir(`${root}web/proofs`)).filter(name => name.endsWith(".cubist"))
  .map(name => name.slice(0, -".cubist".length)).sort();
const totals = {};
let changed = 0;
for (const module of modules) {
  const path = `${root}web/proofs/${module}.cubist`, source = await readFile(path, "utf8");
  const result = rewriteModule(source, { rewrites, skip: new Set(skips[module] ?? []) });
  if (result.source === source) continue;
  let text = result.source;
  try { text = formatMathScript(text); }
  catch (error) { console.log(`${module}: not formatted (${error.message})`); }
  await writeFile(path, text);
  changed++;
  for (const [name, value] of Object.entries(result.applied)) totals[name] = (totals[name] ?? 0) + value;
}
console.log(`${changed} of ${modules.length} modules rewritten: ${JSON.stringify(totals)}`);
