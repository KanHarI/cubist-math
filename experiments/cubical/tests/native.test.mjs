import test from "node:test";
import assert from "node:assert/strict";
import {spawnSync} from "node:child_process";
import {fileURLToPath} from "node:url";
import {interval as I,face as F} from "../lattice.mjs";
const root=fileURLToPath(new URL("../c/",import.meta.url));
const built=spawnSync("make",["-C",root,"all"],{encoding:"utf8"});
assert.equal(built.status,0,built.stderr);
const directory=process.env.CUBICAL_NATIVE_BUILD??"build";
if(!["build","build-sanitize","build-ubsan"].includes(directory))throw Error("Unknown native build.");
const binary=`${root}${directory}/lattice-cli`;
let seed=0x63534348;
function random(n){seed=(Math.imul(seed,1664525)+1013904223)>>>0;return seed%n;}
function expression(depth) {
  if(!depth||random(4)===0){const n=random(8);return n<2?{text:String(n),value:n?I.one:I.zero}:{text:`(v ${n===7?63:n-2})`,value:I.variable(`d${n===7?63:n-2}`)};}
  const a=expression(depth-1),op=random(3);
  if(op===0)return {text:`(not ${a.text})`,value:I.reverse(a.value)};
  const b=expression(depth-1);return {text:`(${op===1?"and":"or"} ${a.text} ${b.text})`,value:(op===1?I.meet:I.join)(a.value,b.value)};
}
test("independent C and JS algebras agree on 1,800 seeded requests",()=>{
  const requests=[],expected=[];
  for(let n=0;n<300;n++) {
    const a=expression(5),b=expression(3),dimension=n%2===0?0:63;
    requests.push(`N ${a.text}`,`E0 ${a.text}`,`E1 ${a.text}`,`SI ${dimension} ${a.text} ${b.text}`,`SF ${dimension} ${a.text} ${b.text}`,`IMPL ${a.text} ${b.text}`);
    expected.push([I,a.value],[F,F.equalEndpoint(a.value,0)],[F,F.equalEndpoint(a.value,1)],
      [I,I.substitute(a.value,`d${dimension}`,b.value)],
      [F,F.substitute(F.equalEndpoint(a.value,1),`d${dimension}`,b.value)],
      [null,F.entails(F.equalEndpoint(a.value,1),F.equalEndpoint(b.value,1))]);
  }
  const result=spawnSync(binary,[],{input:requests.join("\n")+"\n",encoding:"utf8",maxBuffer:32*1024*1024,timeout:20000,killSignal:"SIGKILL"});
  assert.equal(result.status,0,result.stderr);
  const lines=result.stdout.trim().split("\n");assert.equal(lines.length,expected.length);
  for(let i=0;i<lines.length;i++) {
    const actual=JSON.parse(lines[i]),[algebra,value]=expected[i];
    if(algebra)assert.deepEqual(algebra.normalize(actual),value,requests[i]);
    else assert.equal(actual,value,requests[i]);
  }
});
test("native adapter rejects malformed requests and dimension overflow",()=>{
  for(const input of ["N (v 64)","N (v -1)","N (and 0)","N 0 ignored","E2 0","N (not (v 0)"]) {
    const result=spawnSync(binary,[],{input:input+"\n",encoding:"utf8",timeout:5000,killSignal:"SIGKILL"});
    assert.equal(result.status,1,input);assert.equal(result.stdout,"");
  }
});
