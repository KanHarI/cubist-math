import { cubicalSourceFile } from "../web/cubical-sources.mjs";
// Check the selected source import graph once, and report every rejected declaration.
// No theorem-specific replacement, assumption, or legacy certificate is accepted.
import { readFile, writeFile } from 'node:fs/promises';
import { sourceModules, cubicalSourceModules } from '../web/mathscript/modules.mjs';
import createCubical from '../web/dist/cubical.mjs';
import { CubicalProgram } from '../web/cubical-program.mjs';
const args=process.argv.slice(2), all=args.includes('--all');
const selected=all?[...sourceModules,...cubicalSourceModules]:args.filter(x=>!x.startsWith('--'));
if(!selected.length)throw Error('Usage: node tools/audit-cubical.mjs MODULE... | --all');
const program=new CubicalProgram(await createCubical(),name=>readFile(new URL(`../archive/first-library/${cubicalSourceFile(name)}`,import.meta.url),'utf8'));
const budgetOption=args.find(arg=>arg.startsWith('--diagnostic-budget='));
const diagnosticBudget=budgetOption?BigInt(budgetOption.split('=')[1]):null;
if(diagnosticBudget!==null) {
  if(diagnosticBudget<=0n || diagnosticBudget>((1n<<64n)-1n))throw Error('Invalid diagnostic budget.');
  program.kernel.stepBudget=diagnosticBudget;
  program.kernel.module._cb_step_budget(program.kernel.handle,Number(diagnosticBudget&0xffffffffn),Number(diagnosticBudget>>32n));
  // Diagnostic only: stop at the requested budget to locate slow declarations.
  // Production checking still grows its budget; rejection here is not a
  // mathematical counterexample or a claim that the ordinary checker fails.
  program.kernel.withGrowingBudget=operation=>operation();
}
try {
  let count=0;
  await program.check(selected.map(name=>`import ${name};`).join('\n'),'audit',p=>{
    if(args.includes("--verbose") || p.completed>=count+100){count=p.completed;process.stdout.write(`${count} declarations · ${p.instructions} steps · ${p.phase ?? "checked"} ${p.current}\n`);}
  });
  const entries=Object.values(program.symbols), schemas=entries.filter(d=>d.reason?.startsWith('Universe schema:'));
  const failures=entries.filter(d=>!d.verified&&!schemas.includes(d));
  const report={diagnosticBudget:diagnosticBudget?.toString()??null,modules:program.modules.size-1,checked:entries.filter(d=>d.verified).length,schemas:schemas.map(d=>d.binding),failures:failures.map(d=>({binding:d.binding,reason:d.reason})),imports:program.gaps.filter(g=>!g.name)};
  const counts=new Map();for(const d of failures)counts.set(d.reason,(counts.get(d.reason)??0)+1);
  console.log(JSON.stringify({diagnosticBudget:report.diagnosticBudget,modules:report.modules,checked:report.checked,schemas:schemas.length,failed:failures.length,imports:report.imports},null,2));
  for(const [reason,n]of [...counts].sort((a,b)=>b[1]-a[1]).slice(0,30))console.log(`${n}\t${reason}`);
  if(args.includes('--report'))await writeFile(new URL(diagnosticBudget?'../build/cubical-diagnostic-audit.json':'../build/cubical-audit.json',import.meta.url),JSON.stringify(report,null,2)+'\n');
  else if(!all)for(const f of report.failures)console.log(`${f.binding}: ${f.reason}`);
  if(failures.length||report.imports.length)process.exitCode=1;
}finally{program.dispose();}
