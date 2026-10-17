// Repeatable contract mutations in an isolated copy, never the working tree.
// node tools/frontend-generation-mutations.mjs REPORT.json [ID...]
import {mkdtemp,cp,readFile,writeFile,rm,mkdir,readdir} from "node:fs/promises";
import {tmpdir} from "node:os";
import {join,resolve,relative} from "node:path";
import {fileURLToPath} from "node:url";
import {spawnSync,execFileSync} from "node:child_process";
import {createHash} from "node:crypto";
import {testResults,mutationOutcome} from "./frontend-test-results.mjs";

const root=fileURLToPath(new URL("../",import.meta.url));
const [destination,...selected]=process.argv.slice(2);
if(!destination)throw Error("Usage: node tools/frontend-generation-mutations.mjs REPORT.json [ID...]");
const mutation=(id,file,from,to,test,pattern)=>({id,file,from,to,test,pattern});
// Mutate current production boundaries of the adopted contracts. A missing
// site or a broken baseline never counts as a killed mutant.
const mutations=[
  mutation("search-charge","web/translator/fuel.mjs",
    "record.searches++;", "record.searches += 0;",
    "cubist-contracts","^generation\\.G8\\.refusal$"),
  mutation("diagnostic-span","web/translator/elaboration.mjs",
    "start:site.start,end:site.end", "start:site.start,end:site.start",
    "cubist-contracts","^generation\\.(G8|G12_range)\\.refusal$"),
  mutation("binding-label","web/translator/translate.mjs",
    "label=node.label??node.text??node.name", "label=name",
    "frontend-provenance","freshened law and derived parameters"),
  mutation("alpha-label","web/cubist/binding-syntax.mjs",
    "label: token.label ?? binderName(token)", "label: adapter.key(token.bindingId)",
    "frontend-provenance","freshened law and derived parameters"),
  mutation("derived-telescope","web/cubist/retained-interfaces.mjs",
    "const tree=interfaceTree(item);", "const tree=interfaceTree({...item,params:item.kind===\"derived\"?[]:item.params});",
    "frontend-generation","^G11:"),
  mutation("hom-universe","web/cubist/retained-morphism-artifacts.mjs",
    "declare(hom,modelParams(),null,sigma", "declare(hom,modelParams(),builtin(\"U0\",origin),sigma",
    "cubist-contracts","^generation\\.hom_universe\\."),
  mutation("refined-evidence","web/translator/elaboration.mjs",
    "if(!values.size||!this.evidence.length&&!this.inheritedDefinitions.length)return this;", "return this;",
    "frontend-evidence","contextual model evidence remains checked"),
  mutation("synthetic-provenance","web/cubical-program.mjs",
    "!node.synthetic && ownsSource(node,name)", "ownsSource(node,name)",
    "initial-models","generated syntax has local positions"),
  mutation("lint-interface","web/cubist/lint.mjs",
    "&& !publicTelescopes.has(node)", "",
    "frontend-provenance","safe lint preserves"),
  mutation("explicit-head","web/translator/patterns.mjs",
    "constructor.dims && fitting[0].head.kind === \"name\"", "constructor.dims",
    "frontend-generation","explicit path bodies"),
  mutation("reference-spelling","web/cubist/binding-syntax.mjs",
    "const name = adapter.lower(node.resolution, outcomes, options);", "const name = node.spelling;",
    "retained-production","ordinary source and imported inheritance"),
  mutation("lexical-use","web/translator/retained-source-context.mjs",
    "of (item.uses??[]).entries()", "of [].entries()",
    "frontend-invariants","uncolliding parameter, seed 2$"),
  mutation("reservation","web/translator/declarations.mjs",
    "conflict ??= entry;","conflict ??= null;","frontend-publication","definition then inductive"),
  mutation("failed-publication","web/cubical-publication.mjs",
    "transaction?.finish(accept);", "transaction?.finish(true);",
    "frontend-publication","G7:"),
  mutation("interrupted-publication","web/cubical-publication.mjs",
    "if(this.start!==null)this.finish(false);", "if(this.start!==null)this.finish(true);",
    "frontend-publication","^publication interruption:"),
  mutation("rolled-back-inspection","web/cubical-publication.mjs",
    "if(accept)for(const record of records)", "for(const record of records)",
    "frontend-publication","^publication interruption: progress in generated group"),
];
for(const id of selected)if(!mutations.some(m=>m.id===id))throw Error(`Unknown mutation ${id}`);
const chosen=mutations.filter(m=>!selected.length||selected.includes(m.id));
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
    await cp(join(root,name),join(directory,name),{recursive:true,filter:source=>!/(?:^|\/)build(?:\/|$)/.test(relative(root,source))});
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
    const entry={...m,expected:"killed",sourceDigest:hash(original),...classification,status:result.status,error:result.error,
      distinguishingTests:originalTests.passed,reducedCases,events:testResults(result).events??[],stderr:result.stderr};
    report.mutations.push(entry);
    await rm(failures,{recursive:true,force:true});
    console.log(`${m.id}: ${outcome} (expected killed)`);
    if(outcome!=="killed")process.exitCode=1;
    await mkdir(resolve(destination,".."),{recursive:true});
    await writeFile(resolve(destination),JSON.stringify(report,null,2)+"\n");
  }
}finally {await rm(directory,{recursive:true,force:true});}
