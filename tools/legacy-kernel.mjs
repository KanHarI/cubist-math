// The primitive calculus remains a historical comparison oracle, outside the
// production kernel and browser bundle. Its exact source is read from the
// merged pre-migration commit, never from today's kernel directory.
import {execFileSync} from 'node:child_process';
import {existsSync,mkdirSync,readFileSync,readdirSync,writeFileSync,rmSync} from 'node:fs';
import {fileURLToPath,pathToFileURL} from 'node:url';
import {join} from 'node:path';
const root=fileURLToPath(new URL('../',import.meta.url));
export const legacyRevision='bfef585cfe09f4b94a658564dff505cd67855368';
const destination=join(root,'build/reference-kernel',legacyRevision);
export const legacyKernelRoot=join(destination,'kernel/');
const output=join(destination,'web/dist/cubical.mjs');
export function ensureLegacyKernel({wasm=true,build='build'}={}) {
  if(!['build','build-ubsan','build-sanitize'].includes(build))throw Error('Unknown historical native build.');
  const nativeOutput=join(legacyKernelRoot,build,'kernel-cli');
  if(existsSync(nativeOutput)&&(!wasm||existsSync(output)))return;
  mkdirSync(destination,{recursive:true});
  const lock=join(destination,'.build-lock');
  for(let attempts=0;;attempts++) {
    try {mkdirSync(lock);break;}
    catch(error) {if(error.code!=='EEXIST'||attempts>=300)throw error;execFileSync('sleep',['0.1']);}
  }
  try {
    if(!existsSync(join(destination,'source-revision'))) {
      const archive=execFileSync('git',['archive',legacyRevision,'kernel','wasm/cubical_bridge.c'],{cwd:root,maxBuffer:16*1024*1024});
      execFileSync('tar',['-xf','-','-C',destination],{input:archive});
      writeFileSync(join(destination,'source-revision'),legacyRevision+'\n');
    }
    if(readFileSync(join(destination,'source-revision'),'utf8').trim()!==legacyRevision)throw Error('Wrong historical kernel revision.');
    if(!existsSync(nativeOutput)) {
      const flags=build==='build'?[]:[`BUILD=${build}`,
        `CFLAGS=-O1 -g -std=c11 -Wall -Wextra -Wpedantic -Werror -fsanitize=${build==='build-ubsan'?'undefined':'address,undefined'} -fno-sanitize-recover=all -fno-omit-frame-pointer`];
      execFileSync('make',['-C',legacyKernelRoot,...flags,'all'],{stdio:'pipe'});
    }
    if(wasm&&!existsSync(output)) {
      mkdirSync(join(destination,'web/dist'),{recursive:true});
      const exports=readFileSync(join(root,'Makefile'),'utf8').match(/^CUBICAL_EXPORTS = (.*)$/m)[1].slice(1,-1);
      const emcc=existsSync(join(root,'.tools/emsdk/upstream/emscripten/emcc'))?join(root,'.tools/emsdk/upstream/emscripten/emcc'):'emcc';
      execFileSync(emcc,['-O3','-std=c11','-Wall','-Wextra','-Wpedantic','-Werror','-Ikernel/include','-Ikernel/src',
        ...readdirSync(join(destination,'kernel/src')).filter(name=>name.endsWith('.c')).sort().map(name=>'kernel/src/'+name),
        'wasm/cubical_bridge.c','--no-entry','-sMODULARIZE','-sEXPORT_ES6','-sENVIRONMENT=web,worker,node',
        '-sALLOW_MEMORY_GROWTH','-sINITIAL_MEMORY=16777216','-sMAXIMUM_MEMORY=4294967296','-sSTACK_SIZE=2097152',
        '-sABORTING_MALLOC=0','-sFILESYSTEM=0','-sEXPORTED_FUNCTIONS='+exports,
        '-sEXPORTED_RUNTIME_METHODS=["UTF8ToString"]','-o',output],{cwd:destination,stdio:'pipe'});
    }
  } finally {rmSync(lock,{recursive:true});}
}
export default async function createLegacyCubical() {
  ensureLegacyKernel();
  return (await import(pathToFileURL(output).href)).default();
}
