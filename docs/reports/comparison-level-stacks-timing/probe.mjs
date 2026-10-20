// Same checks, module order and shared-WASM lifecycle as fixture shard 1.
import assert from 'node:assert/strict';
import {pathToFileURL} from 'node:url';
import {createHash} from 'node:crypto';
const root=pathToFileURL(process.cwd()+'/');
const {default:createCubical}=await import(new URL('web/dist/cubical.mjs',root));
const {CubicalProgram}=await import(new URL('web/cubical-program.mjs',root));
const {cubistTestModules}=await import(new URL('web/cubist/modules.mjs',root));
const {checkedModule,reported,stated}=await import(new URL('tools/inline-errors.mjs',root));
const {assertFreshBuild,sourceHash}=await import(new URL('tools/build-stamp.mjs',root));
assertFreshBuild();
const kernelHash=sourceHash('kernel'), module=await createCubical();
const originalDispose=CubicalProgram.prototype.dispose;
let observations=[];
CubicalProgram.prototype.dispose=function(...args){
 if(this.kernel?.handle) observations.push({work:this.kernel.work(),arena:this.kernel.arena()});
 return originalDispose.apply(this,args);
};
try{
 for(const name of cubistTestModules.filter((_,i)=>i%4===0)){
  observations=[];
  const start=performance.now();
  const {source,result}=await checkedModule(name,module);
  assert.ok(result.outputs.length||result.evaluations.length||result.prints.length,`${name} declares nothing`);
  const items=reported(source,result,name);
  assert.deepEqual(stated(source),items,`${name}: changed diagnostics or outputs`);
  for(const {label,text} of items) if(label!=='Output')assert.match(text,/^[EKW]\d{3}: /);
  console.log(JSON.stringify({name,ms:performance.now()-start,observations,kernelHash,
   sourceHash:createHash('sha256').update(source).digest('hex')}));
 }
}finally{CubicalProgram.prototype.dispose=originalDispose;}
