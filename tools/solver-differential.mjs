#!/usr/bin/env node
// The argument solver's differential suite: every program of
// tests/fixtures/solver-differential.mjs elaborated, each in a new program,
// and for each of its declarations the verdict (and a refusal's reason), a
// canonical hash of the checked term and type, up to the names of bound
// variables and dimensions and without the kernel's path-application
// annotations (./canonical-hash.mjs), the evaluations' values and the gaps.
//   node tools/solver-differential.mjs [--root=DIR] [--write]
// --root elaborates with another tree's checker, main's say, hashed by this
// tree's canonical-hash.mjs; --write records the result in
// tests/fixtures/solver-differential.json, which is main's. Without --write
// the result is compared with that record, and each difference printed.
import { readFileSync, writeFileSync } from "node:fs";
import { fileURLToPath, pathToFileURL } from "node:url";
import { canonicalHasher } from "./canonical-hash.mjs";
import { programs } from "../tests/fixtures/solver-differential.mjs";

export const fixture = new URL("../tests/fixtures/solver-differential.json", import.meta.url);
const here = fileURLToPath(new URL("../", import.meta.url));

// Each program's elaboration, by the checker of the tree at `root`.
export async function elaborate(root = here) {
  const imp = path => import(pathToFileURL(`${root}/${path}`).href);
  const { default: createCubical } = await imp("web/dist/cubical.mjs");
  const { CubicalProgram } = await imp("web/cubical-program.mjs");
  const { sourceReader } = await imp("tools/module-sources.mjs");
  const module = await createCubical();
  const results = {};
  for (const [name, source] of Object.entries(programs)) {
    const program = new CubicalProgram(module, sourceReader());
    try {
      const result = await program.check(source, name);
      const views = program.checker.definitionViews;
      // Generated unfolding helpers are named by a session serial: hashed by
      // their checked bodies (tools/elaboration-fingerprint.mjs).
      const helper = binding => /__unfolding_\d+$/.test(binding) && views.has(binding);
      let hash;
      hash = canonicalHasher({ definitionName: binding => helper(binding) ? `helper:${hash(views.get(binding).term)}` : binding });
      const declarations = {};
      for (const [binding, symbol] of Object.entries(program.symbols)) {
        if (!binding.startsWith(`${name}__`)) continue;
        const view = views.get(binding);
        declarations[binding] = { verified: !!symbol.verified, reason: symbol.verified ? null : symbol.reason ?? null,
          term: view ? hash(view.term) : null, type: view ? hash(view.type) : null };
      }
      results[name] = { declarations,
        evaluations: (program.evaluations ?? []).filter(evaluation => evaluation.module === name).map(evaluation => `${evaluation.name}: ${evaluation.value}`),
        gaps: result.gaps.filter(gap => gap.module === name || !gap.module).map(gap => `${gap.name ?? ""}: ${gap.reason ?? ""}`) };
    } finally { program.dispose(); }
  }
  return results;
}

// The differences between a recorded result and another, as lines.
export function differences(recorded, results) {
  const lines = [];
  for (const name of new Set([...Object.keys(recorded), ...Object.keys(results)])) {
    const left = recorded[name], right = results[name];
    if (!left || !right) { lines.push(`${name}: ${left ? "not elaborated" : "not recorded"}`); continue; }
    for (const binding of new Set([...Object.keys(left.declarations), ...Object.keys(right.declarations)])) {
      const a = left.declarations[binding], b = right.declarations[binding];
      if (!a || !b) { lines.push(`${binding}: ${a ? "missing" : "new"}`); continue; }
      for (const key of ["verified", "reason", "term", "type"])
        if (a[key] !== b[key]) lines.push(`${binding}: ${key} ${JSON.stringify(a[key])} -> ${JSON.stringify(b[key])}`);
    }
    for (const key of ["evaluations", "gaps"])
      if (JSON.stringify(left[key]) !== JSON.stringify(right[key]))
        lines.push(`${name}: ${key} ${JSON.stringify(left[key])} -> ${JSON.stringify(right[key])}`);
  }
  return lines;
}

if (process.argv[1] && fileURLToPath(import.meta.url) === process.argv[1]) {
  const options = Object.fromEntries(process.argv.slice(2).map(argument => {
    const [key, value = true] = argument.replace(/^--/, "").split("=");
    return [key, value];
  }));
  const results = await elaborate(options.root ?? here);
  if (options.write) {
    writeFileSync(fixture, `${JSON.stringify({ recordedFrom: options.from ?? null, programs: results }, null, 2)}\n`);
    console.log(`Recorded ${Object.keys(results).length} programs.`);
  } else {
    const lines = differences(JSON.parse(readFileSync(fixture, "utf8")).programs, results);
    for (const line of lines) console.log(line);
    console.log(`${Object.keys(results).length} programs, ${lines.length} differences.`);
    if (lines.length) process.exitCode = 1;
  }
}
