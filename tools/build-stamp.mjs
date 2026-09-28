// The build stamp (web/dist/build-stamp.json): a hash of each generated
// artifact's sources, taken before the artifact is built and written once it
// is. The WASM kernel and the translator's runtime copy are both generated
// into web/dist, which is not versioned. A build that no longer matches its
// sources, because they changed afterwards or while it ran, would make a
// test run pass or fail for code it does not contain. So `make wasm`
// rebuilds whatever is stale, and the test runners refuse to start on it.
import { createHash } from "node:crypto";
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import { fileURLToPath } from "node:url";

const root = new URL("../", import.meta.url);
const stampFile = new URL("web/dist/build-stamp.json", root);

// The translator modules copied for the browser (tools/build-cubical-runtime.mjs).
export const runtimeModules = ["core", "lattice", "syntax-graph", "equivalence", "translate", "proof-rewrite",
  "simp-registry", "number-transport", "pushouts", "path-over", "path-algebra", "public-equivalence",
  "dimension-slots", "dependent-transport", "adjointification", "names", "elaboration", "proof-goals", "motives",
  "fuel", "inductive", "match"];

const listed = (directory, keep) => readdirSync(new URL(directory, root)).filter(keep).sort()
  .map(name => `${directory}${name}`);

// Each artifact's sources, as paths from the repository root. The kernel's
// include the Makefile, which holds its compiler flags.
export const buildSources = {
  kernel: () => [...listed("kernel/src/", name => /\.[ch]$/.test(name)), ...listed("kernel/include/", name => name.endsWith(".h")),
    "wasm/cubical_bridge.c", "Makefile"],
  runtime: () => runtimeModules.map(name => `lib/cubical/${name}.mjs`),
};

// A hash of files, by path and content, read through `read`.
export function hashOf(paths, read) {
  const hash = createHash("sha256");
  for (const path of paths) hash.update(path).update("\0").update(read(path)).update("\0");
  return hash.digest("hex");
}

export function sourceHash(kind) {
  if (!buildSources[kind]) throw new Error(`Unknown build ${kind}: expected kernel or runtime.`);
  return hashOf(buildSources[kind](), path => readFileSync(new URL(path, root)));
}

function readStamp() {
  try { return JSON.parse(readFileSync(stampFile, "utf8")); } catch { return {}; }
}

export function writeStamp(kind, hash) {
  mkdirSync(new URL("web/dist/", root), { recursive: true });
  writeFileSync(stampFile, `${JSON.stringify({ ...readStamp(), [kind]: hash }, null, 2)}\n`);
}

// Why each named build does not match its sources; empty when all do.
export function staleBuilds(kinds = Object.keys(buildSources)) {
  const stamp = readStamp();
  return kinds.filter(kind => stamp[kind] !== sourceHash(kind))
    .map(kind => stamp[kind] ? `the ${kind} sources changed since it was built` : `no ${kind} build is recorded`);
}

export function assertFreshBuild(kinds) {
  const stale = staleBuilds(kinds);
  if (stale.length) throw new Error(`web/dist is stale: ${stale.join("; ")}. Run make wasm.`);
}

// node tools/build-stamp.mjs hash KIND | write KIND HASH | check [KIND...]
if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const [command, ...rest] = process.argv.slice(2);
  try {
    if (command === "hash" && rest.length === 1) process.stdout.write(`${sourceHash(rest[0])}\n`);
    else if (command === "write" && rest.length === 2) writeStamp(rest[0], rest[1]);
    else if (command === "check") assertFreshBuild(rest.length ? rest : undefined);
    else throw new Error("Usage: node tools/build-stamp.mjs hash KIND | write KIND HASH | check [KIND...]");
  } catch (error) {
    process.stderr.write(`${error.message}\n`);
    process.exitCode = 1;
  }
}
