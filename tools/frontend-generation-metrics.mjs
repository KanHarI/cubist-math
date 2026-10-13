// Comparable frontend-generation workloads, each in a fresh process/session.
// node tools/frontend-generation-metrics.mjs REPORT.json [REPEATS]
// Search fuel is deterministic. Kernel work depends on cache state; timings
// and memory are observations, not acceptance thresholds.
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
import {parse} from "../web/cubist/parser.mjs";
import {canonicalHasher} from "./canonical-hash.mjs";

assertFreshBuild();
const root = fileURLToPath(new URL("../", import.meta.url));
const sampling = process.argv[2] === "--sample";
const destination = process.argv[2], repeats = sampling ? 1 : Number(process.argv[3] ?? 3);
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
async function sample(name, collectReferences) {
  const source = sources[name];
  if (!source) throw Error(`Unknown workload ${name}`);
  global.gc();
  const before = process.memoryUsage();
  let peak = {nodes:0, bytes:0};
  const checkedTypes = new Map();
  let program = new CubicalProgram(await create(),sourceReader(), {collectReferences,onDeclaration:(module,syntax,result) => {
    const arena = program.kernel.arena();
    peak = {nodes:Math.max(peak.nodes,arena.nodes), bytes:Math.max(peak.bytes,arena.bytes)};
    if (result.status === "checked-native-cubical") checkedTypes.set(`${module}__${result.name}`,result.type);
  }});
  let observation;
  try {
    const start = performance.now();
    const result = await program.check(source,"main");
    const elapsedMs = performance.now()-start;
    global.gc();
    const retained = process.memoryUsage();
    const authored = new Set(Object.entries(program.sources).flatMap(([module,text]) =>
      parse(text).declarations.map(declaration => `${module}__${declaration.name.text}`)));
    const all = Object.values(program.symbols), canonical = canonicalHasher();
    const generated = all.filter(output => output.verified && !authored.has(output.binding));
    const interfaces = all.filter(output => output.verified).map(output => {
      const type = checkedTypes.get(output.binding);
      if (!type) throw Error(`Missing checked interface ${output.binding}`);
      return [output.binding, canonical(type), output.axioms];
    });
    observation = {name,source,elapsedMs,collections:{references:collectReferences,scopePoints:"not implemented",artifacts:"not implemented"},
      work:program.kernel.work(),sourceDigest:hashEntries(Object.entries(program.sources)),
      declarations:result.declarationCount,verified:interfaces.length,
      generatedNames:generated.map(output => output.binding).sort(),
      interfacesDigest:hashEntries(interfaces.map(([binding,type,axioms]) => [binding,JSON.stringify({type,axioms})])),
      assumptions:[...new Set(all.flatMap(output => output.axioms??[]))].sort(),
      declarationFuel:all.map(output => [output.binding,output.searchFuel]),
      retainedReferenceRecords:Object.keys(program.localSymbols).length,
      memory:{before,retained,processMaxRSSBytes:process.resourceUsage().maxRSS*1024},
      peakDeclarationArena:peak,gaps:result.gaps};
  } finally { program.dispose(); program = null; checkedTypes.clear(); }
  global.gc();
  observation.memory.disposed = process.memoryUsage();
  return observation;
}

if (sampling) {
  const observation = await sample(process.argv[3], process.argv[4] === "true");
  process.stdout.write(JSON.stringify(observation));
  process.exit(observation.gaps.length ? 1 : 0);
}
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
  version:2, revision, dirty:!!execFileSync("git", ["status","--porcelain"], {cwd:root, encoding:"utf8"}).trim(),
  frontendDigest:await frontendDigest(), runtime:process.version, cpu:cpus()[0].model,
  platform:`${platform()} ${release()}`, build:JSON.parse(await readFile(join(root,"web/dist/build-stamp.json"),"utf8")),
  limits:"default declaration/search fuel and kernel budgets",
  cacheConditions:"new process, WASM module and kernel session for every workload/mode/repeat",
  peakScope:"arena sampled after declarations; OS process maximum RSS includes startup; retained/released process memory after explicit GC; release drops the program reference",
  samples:[],
};
for (const name of Object.keys(sources)) for (const collectReferences of [false,true]) for (let repeat=0; repeat<repeats; repeat++) {
  const bytes = execFileSync(process.execPath,["--expose-gc",fileURLToPath(import.meta.url),"--sample",name,String(collectReferences)],
    {cwd:root,encoding:"utf8",timeout:120000,maxBuffer:16*1024*1024});
  report.samples.push({...JSON.parse(bytes),repeat});
}
if (await frontendDigest() !== report.frontendDigest) throw Error("Frontend sources changed during measurement.");
await writeFile(resolve(destination),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report.samples.map(({name,elapsedMs,gaps})=>({name,elapsedMs,gaps})),null,2));
