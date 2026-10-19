// One-off diagnostic companion to instrumentation.patch; run in a disposable checkout.
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join, resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
const root=pathToFileURL(process.cwd()+'/');
const {default:createCubical}=await import(new URL('web/dist/cubical.mjs',root));
const {CubicalProgram}=await import(new URL('web/cubical-program.mjs',root));
const {sourceReader}=await import(new URL('tools/module-sources.mjs',root));
const {cubicalKinds}=await import(new URL('web/cubical-kernel.mjs',root));
const {assertFreshBuild}=await import(new URL('tools/build-stamp.mjs',root));assertFreshBuild();
const mode=process.argv[2]??'full',limit=Number(process.argv[3]??50);
if(!['full','body','squash','transport'].includes(mode)||!Number.isInteger(limit)||limit<1||limit>50)throw Error('Choose full, body, squash or transport, and a rewrite limit from 1 to 50.');
const output=resolve(process.argv[4]??join(tmpdir(),'cubist-quotient-trace'));mkdirSync(output,{recursive:true});
const lines=[];const module=await createCubical({printErr:s=>lines.push(s)});
if(typeof module._cb_trace_start!=='function')throw Error('Apply the diagnostic instrumentation patch and rebuild WASM first.');
const p=new CubicalProgram(module,sourceReader(),{collectReferences:false});
try{
 const source=readFileSync(new URL('tests/fixtures/generic-prop-normalization.cubist',root),'utf8');
 const loaded=await p.check(source,'trace');if(!loaded.complete)throw Error(JSON.stringify(loaded.gaps));
 const checked=p.checker.checkSyntax({tag:'DefRef',name:'trace__to_prop'},null,new Map(),new Map());
 const k=p.kernel;let input=checked.expression;const binders=[];
 if(mode!=='full'){
  input=k.definition(input).value;
  while(k.node(input).kind==='Lam'){const n=k.node(input);binders.push({symbol:n.payload,name:n.name,type:n.children[0]});input=n.children[1];}
 }
 if(mode==='squash'||mode==='transport'){
  let exposed=k.head(input);let e=k.node(exposed);if(e.kind!=='App')throw Error('Expected open eliminator application');
  const elim=k.node(e.children[0]);if(elim.kind!=='Elim')throw Error('Expected quotient eliminator');
  let clauses=elim.children[1];for(let i=0;i<2;i++)clauses=k.node(clauses).children[1];
  input=k.node(clauses).children[0];
  if(mode==='transport'){for(;;){const n=k.node(input);if(['Lam','PLam'].includes(n.kind)){binders.push({symbol:n.payload,name:n.name,type:n.children[0],kind:n.kind});input=n.children[1];}else if(n.kind==='App'){const next=k.head(input);if(next===input)break;input=next;}else break;}if(k.node(input).kind!=='Comp')throw Error('Expected squash transport');}
 }
 lines.length=0;module._cb_trace_start(k.handle,limit);
 k.stepBudget=10000000n;k.maxQuerySteps=10000000n;k.setStepBudget(10000000n);k.setDeadline(30000);
 const before={steps:k.work().querySteps,nodes:k.arena().nodes};let outcome;
 try{const result=mode==='full'?k.normalize(input):module._cb_normalize(k.handle,input);if(!result)throw k.failure();outcome={status:'normalized',result};}catch(e){outcome={status:'stopped',kind:e.kind,message:e.message};}
 const after={steps:k.work().querySteps,nodes:k.arena().nodes};
 const events=[],states=new Map();
 for(const line of lines){
  let m=line.match(/^REWRITE (\d+) (\S+) (\d+) (\d+) work=(\d+) nodes=(\d+)/);
  if(m){const [step,rule,before,after,work,nodes]=m.slice(1);events.push({step:+step,rule,before:+before,after:+after,work:+work,nodes:+nodes});continue;}
  m=line.match(/^STATE (\d+) (\d+) ([NW]) (\d+) (\d+) (\d+) (\d+) (\d+),(\d+),(\d+),(\d+)/);
  if(m){const [step,index,mode,entry,current,kind,payload,...children]=m.slice(1);if(!states.has(+step))states.set(+step,[]);states.get(+step).push({index:+index,mode,entry:+entry,current:+current,kind:cubicalKinds[+kind],payload:+payload,children:children.map(Number)});}
 }
 const nodes=new Map(),virtual=new Map();let next=-1;
 const node=id=>virtual.get(id)??k.node(id);
 const snapshots=[];
 for(const [step,frames]of states){
  let focus=events.find(e=>e.step===step).after;
  let entry=frames.at(-1).entry;
  const failures=[],path=[];
  for(let i=frames.length-2;i>=0;i--){const f=frames[i];
   if(f.current===entry){entry=f.entry;continue;}
   const slots=f.children.flatMap((v,i)=>v===entry?[i]:[]);
   if(slots.length!==1){failures.push({index:i,entry,frame:f,matches:slots});entry=f.entry;focus=f.current;continue;}
   const children=[...f.children];children[slots[0]]=focus;focus=next--;virtual.set(focus,{id:focus,kind:f.kind,payload:f.payload,children});entry=f.entry;path.unshift({kind:f.kind,slot:slots[0]});
  }
  snapshots.push({step,root:focus,entry,failures,path,frames});
 }
 function graph(start){const seen=new Set(),todo=[start],kinds={};while(todo.length){const id=todo.pop();if(!id||seen.has(id))continue;seen.add(id);const n=node(id);const record={id,kind:n.kind,payload:n.payload,name:n.name,children:[...n.children]};
   if(n.kind==='DefRef')record.definition=k.definition(id).name;
   if(['PApp','Tube','GlueSystem'].includes(n.kind))record.formula=k.inspectFormula(n.payload);
   nodes.set(id,record);kinds[n.kind]=(kinds[n.kind]??0)+1;todo.push(...n.children.filter(Boolean));}
   return {nodes:seen.size,kinds};}
 const initial=graph(input);for(const b of binders)graph(b.type);for(const e of events){graph(e.before);graph(e.after);}for(const s of snapshots)s.graph=graph(s.root);
 const report={mode,limit,input,binders,initial,...outcome,work:after.steps-before.steps,allocated:after.nodes-before.nodes,events,snapshots,nodes:[...nodes.values()]};
 if(outcome.message!=='Diagnostic contraction checkpoint reached.'||events.length!==limit||snapshots.some(s=>s.failures.length))throw Error('Trace did not reconstruct the requested checkpoint: '+JSON.stringify(outcome));
 const prefix=join(output,`runtime-quotient-rewrites-${mode}-${limit}`);
 writeFileSync(prefix+'.json',JSON.stringify(report,(_,v)=>typeof v==='bigint'?String(v):v,2));writeFileSync(prefix+'.trace',lines.join('\n')+'\n');
 console.log(JSON.stringify({mode,limit,...outcome,initial,work:report.work,allocated:report.allocated,events:events.map(e=>({...e,before:nodes.get(e.before).definition??nodes.get(e.before).kind,after:nodes.get(e.after).kind})),snapshots:snapshots.map(({step,graph,failures,path})=>({step,graph,unmatched:failures.length,path}))}));
}finally{p.dispose();}
