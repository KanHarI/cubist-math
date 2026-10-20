import {pathToFileURL} from 'node:url';
const root=pathToFileURL(process.cwd()+'/');
const {default:createCubical}=await import(new URL('web/dist/cubical.mjs',root));
const {CubicalProgram}=await import(new URL('web/cubical-program.mjs',root));
const {sourceReader}=await import(new URL('tools/module-sources.mjs',root));
const {assertFreshBuild,sourceHash}=await import(new URL('tools/build-stamp.mjs',root));
assertFreshBuild();
const module=await createCubical(), p=new CubicalProgram(module,sourceReader(),{collectReferences:false});
p.kernel.maxQuerySteps=40000000n;
let current=null; const growth=[];
for(const name of ['_cb_head','_cb_normalize','_cb_instr','_cb_rename','_cb_endpoint_term']){
 const original=module[name]; if(typeof original!=='function')throw new Error(name);
 module[name]=(...args)=>{
  const before=p.kernel.arena(), work=p.kernel.work();
  const result=original(...args);
  const after=p.kernel.arena();
  if(after.bytes>before.bytes&&after.bytes>8000000){
   const done=p.kernel.work();
   growth.push({method:name,current,args:args.slice(1),before,after,result,errorKind:module._cb_error_kind(p.kernel.handle),
    querySteps:done.querySteps-work.querySteps,instructionSteps:done.instructionSteps-work.instructionSteps,
    input:name==='_cb_head'||name==='_cb_normalize'?p.kernel.node(args[1]):null});
  }
  return result;
 };
}
try{
 const result=await p.check('import f4_galois_correspondence;','f4_check',event=>{if(event.current)current=event.current;});
 if(result.gaps.length)throw new Error(JSON.stringify(result.gaps));
 console.log(JSON.stringify({kernelHash:sourceHash('kernel'),growth,work:p.kernel.work(),arena:p.kernel.arena()}));
}finally{p.dispose();}
