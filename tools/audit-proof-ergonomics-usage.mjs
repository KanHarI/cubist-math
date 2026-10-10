// Count checked source syntax in the canonical proof corpus, excluding comments
// and the design fixtures under docs/examples.
import {readdirSync,readFileSync} from 'node:fs';
import {parse} from '../web/cubist/parser.mjs';

const root=new URL('../archive/first-library/',import.meta.url);
const features=new Map();
function record(name,file) {
  const entry=features.get(name)??{uses:0,files:new Set()};
  entry.uses++;
  entry.files.add(file);
  features.set(name,entry);
}

for(const file of readdirSync(root).filter(name=>name.endsWith('.cubist'))) {
  const ast=parse(readFileSync(new URL(file,root),'utf8'));
  const seen=new WeakSet(),pending=[ast],introductions=new Map();
  while(pending.length) {
    const node=pending.pop();
    if(!node||typeof node!=='object'||seen.has(node))continue;
    seen.add(node);
    if(node.kind) {
      if(['binderGroup','calc','rw','rfl','ext','pathLambda','pathApply',
        'transport','over','simp','simpOnly','simpa','simpaOnly','simp_rule',
        'simp_set'].includes(node.kind))record(node.kind,file);
      if(node.kind==='let'&&node.value&&node.type)record('typed let',file);
      if(node.kind==='call'&&node.fn?.kind==='name'&&node.fn.name==='apd_path')
        record('apd_path',file);
      if(node.kind==='lambda'&&!node.domain)record('untyped lambda',file);
      if(node.kind==='intro')introductions.set(node.start,(introductions.get(node.start)??0)+1);
    }
    pending.push(...Object.values(node));
  }
  for(const count of introductions.values())if(count>1)record('grouped intro',file);
}

for(const name of ['grouped intro','binderGroup','untyped lambda','typed let',
  'calc','rfl','rw','simp','simpOnly','simpa','simpaOnly','simp_rule','simp_set',
  'pathLambda','pathApply','ext','transport','over','apd_path']) {
  const entry=features.get(name)??{uses:0,files:new Set()};
  console.log(`${name.padEnd(17)} ${String(entry.uses).padStart(3)} uses in ${String(entry.files.size).padStart(3)} files`);
}
