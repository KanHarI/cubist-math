// Reproducible one-run workload for explicit and ergonomic proof examples.
// Counts are deterministic for the checked source; timings are observations.
import {readFile,writeFile} from "node:fs/promises";
import {execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import {cpus} from "node:os";
import {fileURLToPath} from "node:url";
import {benchmark} from "../../../web/benchmark-runner.mjs";
import {parse,tokenize} from "../../../web/mathscript/parser.mjs";

const root=new URL("../../../",import.meta.url);
const examples=new Map([
  ["ergonomics_current","current/arithmetic.cubist"],
  ["ergonomics_implemented","implemented/arithmetic.cubist"],
  ["ergonomics_registered","implemented/registered-simp.cubist"],
]);
const sources=new Map(await Promise.all([...examples].map(async([module,path])=>
  [module,await readFile(new URL(`docs/examples/proof-ergonomics/${path}`,root),"utf8")])));
const readSource=name=>sources.get(name)??readFile(new URL(`web/proofs/${name}.cubist`,root),"utf8");
const report=await benchmark({modules:[...examples.keys()],limitMs:1000,readSource});
if(report.importErrors.length||report.counts.failed||report.counts.blocked||report.counts.optimize)
  throw Error(`Proof-ergonomics workload did not fully check: ${JSON.stringify(report.counts)}`);

const selected=report.declarations.filter(row=>examples.has(row.module)).map(row=>{
  const source=sources.get(row.module);
  const declaration=parse(source).declarations.find(item=>item.name.text===row.name);
  if(!declaration)throw Error(`Missing declaration ${row.module}.${row.name}`);
  return {...row,sourceTokens:tokenize(source.slice(declaration.start,declaration.end)).length-1};
});
const snapshot={
  version:1,generatedAt:report.generatedAt,
  revision:execFileSync("git",["rev-parse","HEAD"],{cwd:fileURLToPath(root),encoding:"utf8"}).trim(),
  dirty:!!execFileSync("git",["status","--porcelain"],{cwd:fileURLToPath(root),encoding:"utf8"}).trim(),
  runtime:process.version,cpu:cpus()[0]?.model,
  method:"One checked import graph, source order, imports shared, inspector references disabled, one 1000 ms deadline per declaration. Candidate visits count every term node considered by rw/simp, including failed rule traversals and premise search. Native steps count checker queries. Arena values snapshot the cumulative kernel at the final check; they are not allocation deltas. Elapsed times are one observation and not a speedup estimate.",
  modules:Object.fromEntries([...examples].map(([name,path])=>[name,{
    path:`docs/examples/proof-ergonomics/${path}`,
    sha256:createHash("sha256").update(sources.get(name)).digest("hex"),
  }])),
  graph:{modules:report.modules,counts:report.counts,elapsedSeconds:report.elapsedSeconds},
  selected,
};
const destination=new URL("./rewrite-work.json",import.meta.url);
await writeFile(destination,JSON.stringify(snapshot,null,2)+"\n");
console.log(`Wrote ${fileURLToPath(destination)}; ${selected.length} example declarations checked.`);
