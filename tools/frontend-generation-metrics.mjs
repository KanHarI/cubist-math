// Comparable frontend-generation workloads, run in fresh kernel sessions.
// node tools/frontend-generation-metrics.mjs REPORT.json [REPEATS]
// Timing is observational; kernel work and arena counts are deterministic.
import {createHash} from "node:crypto";
import {execFileSync} from "node:child_process";
import {readFile, readdir, writeFile} from "node:fs/promises";
import {cpus, platform, release} from "node:os";
import {fileURLToPath} from "node:url";
import {join, relative, resolve} from "node:path";
import create from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {sourceReader} from "./module-sources.mjs";
import {assertFreshBuild} from "./build-stamp.mjs";

assertFreshBuild();
const root = fileURLToPath(new URL("../", import.meta.url));
const destination = process.argv[2], repeats = Number(process.argv[3] ?? 3);
if (!destination || !Number.isSafeInteger(repeats) || repeats < 1)
  throw Error("Usage: node tools/frontend-generation-metrics.mjs REPORT.json [positive repeat count]");
const sources = {
  algebra: "import hlevels; import algebra;",
  inheritance: `import hlevels; import nat;
def outside : Nat := zero;
theory P(U < UU0) { M : set U; c : M; op(x : Nat, y : M) : M; def helper(y : M) : M := op(outside, y); law l(y : M) : helper(y) = y; }
theory Q(U < UU0) extends P {}
theory R(U < UU0) extends Q {}
def meaning(S : R(U0), y : S.M) : S.op(zero, y) = y := S.l(y);`,
  fold: `import hlevels; import algebra; import nat;
free W(A : U0) : Monoid(U0) on A;
def computation : W.fold(Nat, nat_additive.monoid, fun (x : Nat) => x).map(W.gen(succ(zero))) = succ(zero) { rfl; }`,
};
const hashEntries = entries => {
  const hash = createHash("sha256");
  for (const [name, bytes] of entries.sort(([a],[b]) => a.localeCompare(b)))
    hash.update(name).update("\0").update(bytes).update("\0");
  return hash.digest("hex");
};
async function frontendDigest() {
  const paths = [];
  async function visit(directory) {
    for (const entry of await readdir(directory, {withFileTypes:true})) {
      if (entry.name === "dist") continue; // Loader/WASM are pinned by the build stamp.
      const path = join(directory, entry.name);
      if (entry.isDirectory()) await visit(path);
      else if (entry.isFile() && path.endsWith(".mjs")) paths.push(path);
    }
  }
  await visit(join(root, "web"));
  paths.push(fileURLToPath(import.meta.url));
  return hashEntries(await Promise.all(paths.map(async path => [relative(root,path), await readFile(path)])));
}
const revision = execFileSync("git", ["rev-parse","HEAD"], {cwd:root, encoding:"utf8"}).trim();
const report = {
  version:1, revision, dirty:!!execFileSync("git", ["status","--porcelain"], {cwd:root, encoding:"utf8"}).trim(),
  frontendDigest:await frontendDigest(), runtime:process.version, cpu:cpus()[0].model,
  platform:`${platform()} ${release()}`, build:JSON.parse(await readFile(join(root,"web/dist/build-stamp.json"),"utf8")),
  limits:"default declaration/search fuel and kernel budgets",
  peakScope:"arena nodes/bytes observed after each declaration; not whole-process peak memory",
  samples:[],
};
for (const [name,source] of Object.entries(sources)) for (let repeat=0; repeat<repeats; repeat++) {
  let peak = {nodes:0, bytes:0};
  const program = new CubicalProgram(await create(),sourceReader(), {onDeclaration:() => {
    const arena = program.kernel.arena();
    peak = {nodes:Math.max(peak.nodes,arena.nodes), bytes:Math.max(peak.bytes,arena.bytes)};
  }});
  try {
    const start = performance.now();
    const result = await program.check(source,"main");
    const elapsedMs = performance.now()-start;
    report.samples.push({name,repeat,source,elapsedMs, work:program.kernel.work(),
      sourceDigest:hashEntries(Object.entries(program.sources)),
      declarations:result.declarationCount, peakDeclarationArena:peak, gaps:result.gaps});
    if (result.gaps.length) process.exitCode=1;
  } finally { program.dispose(); }
}
if (await frontendDigest() !== report.frontendDigest) throw Error("Frontend sources changed during measurement.");
await writeFile(resolve(destination),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report.samples.map(({name,elapsedMs,gaps})=>({name,elapsedMs,gaps})),null,2));
