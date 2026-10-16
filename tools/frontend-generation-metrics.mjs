// Comparable frontend-generation workloads, each in a fresh process/session.
// node tools/frontend-generation-metrics.mjs REPORT.json [REPEATS]
// Search fuel is deterministic. Kernel work depends on cache state; timings
// and memory are observations, not acceptance thresholds.
import {serialize} from "node:v8";
import {setImmediate} from "node:timers/promises";
import {execFileSync} from "node:child_process";
import {readFile, readdir, writeFile} from "node:fs/promises";
import {cpus, platform, release} from "node:os";
import {fileURLToPath} from "node:url";
import {join, relative, resolve} from "node:path";
import create from "../web/dist/cubical.mjs";
import {CubicalProgram} from "../web/cubical-program.mjs";
import {sourceReader, archiveReader} from "./module-sources.mjs";
import {archiveModules} from "../web/cubist/modules.mjs";
import {assertFreshBuild} from "./build-stamp.mjs";
import {parse} from "../web/cubist/parser.mjs";
import {canonicalHasher} from "./canonical-hash.mjs";
import {hashEntries, byName, jsonDigest, digestFormats, compactSamples} from "./frontend-generation-evidence.mjs";

assertFreshBuild();
const root = fileURLToPath(new URL("../", import.meta.url));
const sampling = process.argv[2] === "--sample";
const inventoryOnly = process.argv[2] === "--corpus";
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
const modes={
  "refs-off":{collectReferences:false,collectScopes:false,collectGeneration:false},
  "refs-on":{collectReferences:true,collectScopes:false,collectGeneration:false},
  "scopes-on":{collectReferences:true,collectScopes:true,collectGeneration:false},
  "artifacts-on":{collectReferences:true,collectScopes:false,collectGeneration:true},
  "both-on":{collectReferences:true,collectScopes:true,collectGeneration:true},
};
async function sample(name, mode) {
  const options=modes[mode];
  if(!options)throw Error(`Unknown collection mode ${mode}`);
  const source = sources[name];
  if (!source) throw Error(`Unknown workload ${name}`);
  global.gc();
  const before = process.memoryUsage();
  let peak = {nodes:0, bytes:0};
  const checkedTypes = new Map();
  let program = new CubicalProgram(await create(),sourceReader(), {...options,onDeclaration:(module,syntax,result) => {
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
      return [output.binding, canonical(type), [...output.axioms].sort()];
    });
    // Size only inert retained data, preserving sharing. Take process memory
    // before this serialization, which allocates a separate temporary buffer.
    const scopes=options.collectScopes?{points:program.scopePoints,replay:program.scopeReplay.snapshot()}:null;
    const artifacts=options.collectGeneration?program.generation:null;
    const retainedGraph={scopePoints:program.scopePoints.size,
      availableScopePoints:[...program.scopePoints.values()].filter(point=>point.available).length,
      generatedDeclarations:[...program.generation.values()].reduce((n,groups)=>n+groups.reduce((n,g)=>n+g.declarations.length,0),0),
      scopeBytes:scopes?serialize(scopes).byteLength:0,artifactBytes:artifacts?serialize(artifacts).byteLength:0,
      combinedBytes:serialize({scopes,artifacts}).byteLength};
    observation = {name,source,elapsedMs,mode,collections:{references:options.collectReferences,
      scopePoints:options.collectScopes,artifacts:options.collectGeneration},retainedGraph,
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
  return observation;
}

async function corpusInventory() {
  const program = new CubicalProgram(await create(), archiveReader("benchmark"), {collectReferences:false});
  try {
    const result = await program.check(archiveModules.map(name => `import ${name};`).join("\n"), "benchmark");
    const symbols = Object.values(program.symbols), canonical = canonicalHasher();
    const assumptions = [...program.checker.assumptions].sort(byName).map(([binding,type]) =>
      ({binding, label:program.checker.assumptionLabels.get(binding) ?? binding, typeDigest:canonical(type)}));
    if (result.gaps.length || symbols.some(output => !output.verified)) throw Error("Corpus did not check completely");
    return {declarations:result.declarationCount, entryModules:archiveModules.length,
      loadedModules:Object.keys(program.sources).filter(name => name !== "benchmark").sort(),
      verified:symbols.filter(output => output.verified).length, sourceDigest:hashEntries(Object.entries(program.sources)),
      assumptions, assumptionDependenciesDigest:jsonDigest(symbols.map(output =>
        [output.binding, [...output.axioms].sort()]).sort(byName)), gaps:result.gaps};
  } finally { program.dispose(); }
}

if (inventoryOnly) {
  process.stdout.write(JSON.stringify(await corpusInventory()));
  process.exit(0);
}

if (sampling) {
  const observation = await sample(process.argv[3], process.argv[4]);
  // Sample after the measurement frame releases all local aliases, not only
  // its program variable. Let the completed async stack leave the current
  // turn too, so its last check result cannot still root the program.
  await setImmediate();
  global.gc();
  observation.memory.disposed = process.memoryUsage();
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
  paths.push(...["frontend-generation-metrics.mjs", "frontend-generation-evidence.mjs", "canonical-hash.mjs", "module-sources.mjs"]
    .map(name => fileURLToPath(new URL(name, import.meta.url))));
  return hashEntries(await Promise.all(paths.map(async path => [relative(root,path), await readFile(path)])));
}
const revision = execFileSync("git", ["rev-parse","HEAD"], {cwd:root, encoding:"utf8"}).trim();
const report = {
  version:4, digestFormats, revision, dirty:!!execFileSync("git", ["status","--porcelain"], {cwd:root, encoding:"utf8"}).trim(),
  frontendDigest:await frontendDigest(), runtime:process.version, cpu:cpus()[0].model,
  platform:`${platform()} ${release()}`, build:JSON.parse(await readFile(join(root,"web/dist/build-stamp.json"),"utf8")),
  limits:"default declaration/search fuel and kernel budgets",
  cacheConditions:"new process, WASM module and kernel session for every workload/mode/repeat",
  peakScope:"arena sampled after declarations; OS process maximum RSS includes startup; retained/released process memory after explicit GC; peak RSS includes graph serialization; release sampled after the measurement frame returns and the event-loop turn completes",
  retainedEncoding:"node:v8 serialize of inert scope points/replay inputs and generated artifacts; sharing preserved; bytes are not retained heap",
  samples:[],
};
for (const name of Object.keys(sources)) for (const mode of Object.keys(modes)) for (let repeat=0; repeat<repeats; repeat++) {
  const bytes = execFileSync(process.execPath,["--expose-gc",fileURLToPath(import.meta.url),"--sample",name,mode],
    {cwd:root,encoding:"utf8",timeout:120000,maxBuffer:16*1024*1024});
  report.samples.push({...JSON.parse(bytes),repeat});
}
Object.assign(report, compactSamples(report.samples));
report.corpus = JSON.parse(execFileSync(process.execPath,[fileURLToPath(import.meta.url),"--corpus"],
  {cwd:root,encoding:"utf8",timeout:300000,maxBuffer:16*1024*1024}));
if (await frontendDigest() !== report.frontendDigest) throw Error("Frontend sources changed during measurement.");
await writeFile(resolve(destination),JSON.stringify(report,null,2)+"\n");
console.log(JSON.stringify(report.samples.map(({name,mode,elapsedMs,retainedGraph})=>({name,mode,elapsedMs,retainedGraph})),null,2));
