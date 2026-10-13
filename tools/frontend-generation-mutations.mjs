// Repeatable contract mutations in an isolated copy, never the working tree.
// node tools/frontend-generation-mutations.mjs REPORT.json [--audit] [ID...]
import {mkdtemp,cp,readFile,writeFile,rm,mkdir,readdir} from "node:fs/promises";
import {tmpdir} from "node:os";
import {join,resolve} from "node:path";
import {fileURLToPath} from "node:url";
import {spawnSync,execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import {testResults,mutationOutcome} from "./frontend-test-results.mjs";

const root=fileURLToPath(new URL("../",import.meta.url));
const args=process.argv.slice(2),destination=args.shift(),audit=args.includes("--audit");
const selected=args.filter(arg=>arg!=="--audit");
if(!destination)throw Error("Usage: node tools/frontend-generation-mutations.mjs REPORT.json [--audit] [ID...]");
const mutation=(id,file,from,to,test,pattern,expected="killed")=>({id,file,from,to,test,pattern,expected});
// These four sites exist on the CB0 base. Later-phase mutations from #223
// are deferred with their distinguishing witnesses in the CB0 report; a
// missing site never counts as a killed mutant.
export const mutations=[
  mutation("reference-spelling","web/cubist/references.mjs",
    '? {...n, kind: "name", name: n.binding}', '? {...n, kind: "name", name: n.spelling}',
    "references","lowering references"),
  mutation("lexical-use","web/translator/theories.mjs",
    "if(!d.uses?.length)return {env,notation:[[SELECTION,null]]};","if(true)return {env,notation:[[SELECTION,null]]};",
    "frontend-invariants","uncolliding parameter, seed 3$"),
  mutation("reservation","web/translator/declarations.mjs",
    "conflict ??= entry;","conflict ??= null;","frontend-publication","definition then inductive"),
  mutation("failed-publication","web/cubical-program.mjs",
    "transaction?.finish(accept); transaction=null;", "transaction?.finish(true); transaction=null;",
    "frontend-publication","G7:"),
];
for(const id of selected)if(!mutations.some(m=>m.id===id))throw Error(`Unknown mutation ${id}`);
const chosen=mutations.filter(m=>(audit||m.expected==="killed")&&(!selected.length||selected.includes(m.id)));
const directory=await mkdtemp(join(tmpdir(),"cubist-generation-mutations-"));
const report={version:2,adoptedFrom:"49499aa1c56c1b345eb0021468123cec377fb4b8",dirty:!!execFileSync("git",["status","--porcelain"],{cwd:root,encoding:"utf8"}).trim(),revision:execFileSync("git",["rev-parse","HEAD"],{cwd:root,encoding:"utf8"}).trim(),
  limits:{processMs:60000,testMs:45000,maxBufferBytes:8*1024*1024,checker:"unchanged defaults",cases:8},mutations:[]};
const hash=source=>createHash("sha256").update(source).digest("hex");
const run=m=>{
  const env={...process.env,CUBIST_GENERATION_CASES:"8"};delete env.NODE_TEST_CONTEXT;
  const result=spawnSync(process.execPath,["--test","--test-reporter=./tools/frontend-test-reporter.mjs","--test-timeout=45000",`--test-name-pattern=${m.pattern}`,
    ...[m.test].flat().map(name=>`tests/${name}.test.mjs`)],
    {cwd:directory,env,encoding:"utf8",timeout:60000,maxBuffer:8*1024*1024});
  return {status:result.status,error:result.error?.message,signal:result.signal,log:result.stdout??"",stderr:result.stderr??""};
};
try {
  for(const name of ["web","tests","tools","library","cubist-tests","archive","kernel","wasm","Makefile","cli","package.json"])
    await cp(join(root,name),join(directory,name),{recursive:true,filter:source=>!/(?:^|\/)build(?:\/|$)/.test(source)});
  for(const m of chosen) {
    const path=join(directory,m.file),original=await readFile(path,"utf8");
    const occurrences=original.split(m.from).length-1;
    if(occurrences!==1)throw Error(`${m.id}: expected one mutation site, found ${occurrences}`);
    const baseline=run(m);
    const originalTests=testResults(baseline);
    if(baseline.status!==0||originalTests.invalid||!originalTests.passed.length)
      throw Error(`${m.id}: baseline failed or no tests ran (status ${baseline.status}, signal ${baseline.signal}, error ${baseline.error??"none"})\n${baseline.log}`);
    let result;
    try {await writeFile(path,original.replace(m.from,m.to));result=run(m);}
    finally {await writeFile(path,original);}
    const classification=mutationOutcome(result,originalTests.passed),{outcome}=classification;
    const failures=join(directory,"build/frontend-generation-failures");
    const reducedCases=await Promise.all((await readdir(failures).catch(error=>{
      if(error.code==="ENOENT")return [];throw error;
    })).map(async name=>JSON.parse(await readFile(join(failures,name),"utf8"))));
    const entry={...m,sourceDigest:hash(original),...classification,status:result.status,error:result.error,
      distinguishingTests:originalTests.passed,reducedCases,events:testResults(result).events??[],stderr:result.stderr};
    report.mutations.push(entry);
    await rm(failures,{recursive:true,force:true});
    console.log(`${m.id}: ${outcome} (expected ${m.expected})`);
    if(outcome!==m.expected)process.exitCode=1;
    await mkdir(resolve(destination,".."),{recursive:true});
    await writeFile(resolve(destination),JSON.stringify(report,null,2)+"\n");
  }
}finally {await rm(directory,{recursive:true,force:true});}
