// Repeatable contract mutations in an isolated copy, never the working tree.
// node tools/frontend-generation-mutations.mjs REPORT.json [--audit] [ID...]
import {mkdtemp,cp,readFile,writeFile,rm,mkdir} from "node:fs/promises";
import {tmpdir} from "node:os";
import {join,resolve} from "node:path";
import {fileURLToPath} from "node:url";
import {spawnSync,execFileSync} from "node:child_process";
import {createHash} from "node:crypto";

const root=fileURLToPath(new URL("../",import.meta.url));
const args=process.argv.slice(2),destination=args.shift(),audit=args.includes("--audit");
const selected=args.filter(arg=>arg!=="--audit");
if(!destination)throw Error("Usage: node tools/frontend-generation-mutations.mjs REPORT.json [--audit] [ID...]");
const mutation=(id,file,from,to,test,pattern,expected="killed")=>({id,file,from,to,test,pattern,expected});
export const mutations=[
  mutation("binding-label","web/translator/translate.mjs",
    "{key:name,name:node.label??name,start:node.start,end:node.end}","{key:name,name,start:node.start,end:node.end}",
    "frontend-provenance","FG5: freshened law"),
  mutation("alpha-label","web/cubist/scopes.mjs",
    "{ ...binder, text: other, label: binder.label ?? binderName(binder) }", "{ ...binder, text: other }",
    "frontend-provenance","FG5: freshened law"),
  mutation("lexical-use","web/translator/theories.mjs",
    "if(!d.uses?.length)return {env,notation:[[SELECTION,null]]};","if(true)return {env,notation:[[SELECTION,null]]};",
    "frontend-invariants","seed 3$"),
  mutation("reference-spelling","web/cubist/references.mjs",
    '? {...n, kind: "name", name: n.binding}', '? {...n, kind: "name", name: n.spelling}',
    "references","lowering references"),
  mutation("derived-telescope","web/cubist/scopes.mjs",
    'derived: n => parameterScopes(n, ["type", "value"], true)', 'derived: n => []',
    "frontend-generation","G11:"),
  mutation("hom-universe","web/cubist/morphisms.mjs",
    'declare(hom, `${models([])} :=', 'declare(hom, `${models([])} : U0 :=',
    "frontend-generation","G2:"),
  mutation("refined-evidence","web/translator/elaboration.mjs",
    "if(!values.size||!this.evidence.length)return this;", "return this;",
    "frontend-evidence","contextual model evidence remains checked"),
  mutation("reservation","web/translator/declarations.mjs",
    "if (previous && previous.owner !== owner || seen.has(entry.name) && seen.get(entry.name) !== entry.declaration) return entry;",
    "if (false) return entry;","frontend-publication","definition then inductive"),
  mutation("failed-publication","web/cubical-program.mjs",
    "transaction?.finish(accept); transaction=null;", "transaction?.finish(true); transaction=null;",
    "frontend-publication","G7:"),
  mutation("synthetic-provenance","web/translator/translate.mjs",
    "if(n.synthetic&&scope.unit.references)scope=scope.withUnit(scope.unit.with({references:null}));", "// mutant: keep synthetic reference sink",
    "initial-models","notation without a caller selection"),
  mutation("fallback-eligibility","web/translator/match.mjs",
    "if(!shape.positions)throw primary;", "// mutant: try coherence for a nonrecursive boundary",
    "frontend-generation","G8:"),
  mutation("lint-interface","web/cubist/lint.mjs",
    "&& !publicTelescopes.has(node)", "",
    "frontend-generation","G5:"),
  // Named historical survivors are probes, excluded from the required-kill
  // CI set only with their reachability analysis in the accompanying report.
  mutation("fresh-label","web/translator/translate.mjs",
    "scope.fresh(n.name.label??n.name.text)","scope.fresh(n.name.text)",
    "frontend-provenance","FG5:","survived"),
  mutation("recursive-update","web/translator/match.mjs",
    "at = at.alias(RECURSIVE, updated);", "// mutant: keep previous private recursion entry",
    ["declared-match","frontend-evidence","theory-hygiene","frontend-generation"],"recurs|FG4:|generalized","survived"),
  mutation("recursive-source-guard","web/translator/translate.mjs",
    "if(recursive?.source!==n.fn.name)throw Error(selfReference(n.fn.name));", "// mutant: omit generated source guard",
    ["declared-match","frontend-evidence","theory-hygiene","frontend-generation"],"recurs|FG4:|generalized","survived"),
  mutation("hlevel-globals","web/translator/initial-models.mjs",
    'new Set([N, T, "refl",', 'new Set([N, T, "refl", "IsSet", "IsProp",',
    "theory-hygiene","freshened parameters","survived"),
  mutation("explicit-head","web/translator/patterns.mjs",
    'implicitPath=constructor.dims&&fitting[0].head.kind==="name"', 'implicitPath=constructor.dims',
    "frontend-generation","explicit path bodies"),
];
for(const id of selected)if(!mutations.some(m=>m.id===id))throw Error(`Unknown mutation ${id}`);
const chosen=mutations.filter(m=>(audit||m.expected==="killed")&&(!selected.length||selected.includes(m.id)));
const directory=await mkdtemp(join(tmpdir(),"cubist-generation-mutations-"));
const report={version:1,revision:execFileSync("git",["rev-parse","HEAD"],{cwd:root,encoding:"utf8"}).trim(),
  limits:{processMs:60000,testMs:45000,maxBufferBytes:8*1024*1024,checker:"unchanged defaults",cases:8},mutations:[]};
const hash=source=>createHash("sha256").update(source).digest("hex");
const run=m=>{
  const env={...process.env,CUBIST_GENERATION_CASES:"8"};delete env.NODE_TEST_CONTEXT;
  const result=spawnSync(process.execPath,["--test","--test-reporter=tap","--test-timeout=45000",`--test-name-pattern=${m.pattern}`,
    ...[m.test].flat().map(name=>`tests/${name}.test.mjs`)],
    {cwd:directory,env,encoding:"utf8",timeout:60000,maxBuffer:8*1024*1024});
  return {status:result.status,error:result.error?.message,signal:result.signal,log:(result.stdout??"")+(result.stderr??"")};
};
try {
  for(const name of ["web","tests","tools","library","cubist-tests","archive","kernel","wasm","Makefile","cli","package.json"])
    await cp(join(root,name),join(directory,name),{recursive:true,filter:source=>!/(?:^|\/)build(?:\/|$)/.test(source)});
  for(const m of chosen) {
    const path=join(directory,m.file),original=await readFile(path,"utf8");
    const occurrences=original.split(m.from).length-1;
    if(occurrences!==1)throw Error(`${m.id}: expected one mutation site, found ${occurrences}`);
    const baseline=run(m);
    if(baseline.status!==0||!/# pass [1-9]/.test(baseline.log))throw Error(`${m.id}: baseline failed or no tests ran\n${baseline.log}`);
    let result;
    try {await writeFile(path,original.replace(m.from,m.to));result=run(m);}
    finally {await writeFile(path,original);}
    const invalid=result.error||result.signal||/SyntaxError:|ERR_MODULE_NOT_FOUND|ENOENT|testTimeoutFailure/.test(result.log);
    const outcome=invalid?"invalid":result.status===0?"survived":result.log.includes("ERR_ASSERTION")?"killed":"unclassified";
    const entry={...m,sourceDigest:hash(original),outcome,status:result.status,error:result.error,
      failedTests:[...result.log.matchAll(/not ok \d+ - (.+)/g)].map(match=>match[1]),log:result.log};
    report.mutations.push(entry);
    console.log(`${m.id}: ${outcome} (expected ${m.expected})`);
    if(outcome!==m.expected)process.exitCode=1;
    await mkdir(resolve(destination,".."),{recursive:true});
    await writeFile(resolve(destination),JSON.stringify(report,null,2)+"\n");
  }
}finally {await rm(directory,{recursive:true,force:true});}
