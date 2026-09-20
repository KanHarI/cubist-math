import {readFile,readdir,writeFile} from "node:fs/promises";
import {parse} from "../../web/mathscript/parser.mjs";
import {Translator} from "./translate.mjs";
import {execFileSync} from "node:child_process";
import {fileURLToPath} from "node:url";
const root=new URL("../../web/proofs/",import.meta.url),modules=new Map(),results=new Map(),active=new Set();
for(const file of (await readdir(root)).filter(n=>n.endsWith(".proof")&&!n.endsWith(".construction.proof")).sort()) {
  const source=await readFile(new URL(file,root),"utf8");modules.set(file.slice(0,-6),{source,ast:parse(source)});
}
function visit(name) {
  if(name==="prelude")return {env:new Map()}; // no old-kernel exports are admitted
  if(results.has(name))return results.get(name);
  if(active.has(name))throw Error(`Cyclic source import ${name}`);
  const module=modules.get(name);if(!module)throw Error(`Missing source ${name}`);
  active.add(name);const imported=new Map();
  for(const dependency of module.ast.imports)for(const [n,value]of visit(dependency).env)imported.set(n,value);
  const result=new Translator().translate(module.source,imported);
  results.set(name,result);active.delete(name);return result;
}
const start=performance.now();
for(const name of modules.keys())visit(name);
const sourceRevision=execFileSync("git",["log","-1","--format=%H","--","web/proofs"],{cwd:fileURLToPath(new URL("../../",import.meta.url)),encoding:"utf8"}).trim();
const report={scope:"Actual translation into the checked CCHM structural/path/composition fragment. Glue, universe composition, HITs and the strict Id bridge are not implemented; this is not full cubical migration.",sourceRevision,
  elapsedMilliseconds:Math.round(performance.now()-start),peakRssBytes:process.resourceUsage().maxRSS*1024,
  checked:0,untranslated:0,modules:[]};
for(const [name,result]of [...results].sort(([a],[b])=>a.localeCompare(b))) {
  const declarations=result.declarations.map(({name,status,reason})=>({name,status,...reason?{reason}:{}}));
  report.checked+=declarations.filter(d=>d.status==="checked-cubical-fragment").length;
  report.untranslated+=declarations.filter(d=>d.status==="not-translated").length;
  report.modules.push({module:name,declarations});
}
await writeFile(new URL("../../docs/cubical/translation-results.json",import.meta.url),JSON.stringify(report,null,2)+"\n");
console.log(`${report.checked} declarations checked in the cubical fragment; ${report.untranslated} explicit gaps; ${report.elapsedMilliseconds} ms.`);
