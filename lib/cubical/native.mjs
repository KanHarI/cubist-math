// Inert serialization adapter for the independent native checker. No JS type
// checking is used to approve a native result. The same constructor stream can
// target WASM's integer-handle API instead of the native test process.
import {spawnSync} from "node:child_process";
import {fileURLToPath} from "node:url";
import {interval as I,face as F} from "./lattice.mjs";
import {bindDimensions} from "./dimension-slots.mjs";
const kinds=["","U","Var","Pi","Lam","App","Sigma","Pair","Fst","Snd","Nat","Zero","Succ","NatRec","Unit","Point","Path","PLam","PApp","Comp","Tube","Void","Abort","W","Sup","WRec","Sum","Inl","Inr","SumRec","UnitRec","Glue","GlueSystem","GlueTerm","Unglue","DefRef","Pushout","PushLeft","PushRight","PushPath","PushElim","HComp","Trans"];
const nativeRoot=fileURLToPath(new URL("../../kernel/",import.meta.url));

export function nativeRequest(term,expected=null,assumptions=[],{normalize=true,definitions=[],unfoldingHints=[]}={}) {
  const lines=[],names=new Map(),reverse=new Map(),formulas=new Map(),references=new Map();let terms=0;
  const name=n=>{if(!names.has(n)){names.set(n,names.size+1);reverse.set(names.get(n),n);}return names.get(n);};
  const node=(tag,payload=0,children=[])=>{
    const kind=kinds.indexOf(tag);if(kind<1)throw Error(`Unsupported native term ${tag}`);
    const padded=[...children];while(padded.length<4)padded.push(0);
    lines.push(`N ${kind} ${payload} ${padded.join(" ")}`);return ++terms;
  };
  const formula=(sort,raw,dims)=>{
    const value=(sort?F:I).normalize(raw),clauses=value.map(c=>{
      let pos=0n,neg=0n;
      for(const literal of c){const n=literal.slice(0,-2);if(!dims.has(n))throw Error(`Unbound serialized dimension ${n}`);const bit=1n<<BigInt(dims.get(n));if(literal.endsWith("1"))pos|=bit;else neg|=bit;}
      return [pos,neg];
    }).sort((a,b)=>String(a).localeCompare(String(b)));
    const key=`${sort}:`+clauses.map(c=>c.join(",")).join(";");
    if(!formulas.has(key)){formulas.set(key,formulas.size+1);lines.push(`F ${sort} ${clauses.length} ${clauses.map(c=>c.join(" ")).join(" ")}`);}
    return formulas.get(key);
  };
  const encode=(t,dims=new Map())=>{
    if(!t)throw Error("Missing native input term.");
    const child=x=>encode(x,dims);
    switch(t.tag){
      case "U":return node(t.tag,t.level);
      case "Var":return node(t.tag,name(t.name));
      case "Ref":{
        if(!references.has(t.name))throw Error(`Unknown checked definition ${t.name}`);
        return references.get(t.name);
      }
      case "Nat":case "Zero":case "Unit":case "Point":case "Void":return node(t.tag);
      case "Pi":case "Lam":case "Sigma":case "W":return node(t.tag,name(t.name),[child(t.domain),child(t.body)]);
      case "App":return node(t.tag,0,[child(t.fn),child(t.arg)]);
      case "Pair":return node(t.tag,0,[child(t.as),child(t.first),child(t.second)]);
      case "Fst":case "Snd":return node(t.tag,0,[child(t.pair)]);
      case "Succ":return node(t.tag,0,[child(t.value)]);
      case "NatRec":return node(t.tag,0,[child(t.motive),child(t.zero),child(t.step),child(t.value)]);
      case "HComp":case "Trans": {
        const {dim,inner}=bindDimensions(t,dims);
        const family=encode(t.family,t.tag==="HComp"?dims:inner),base=child(t.base);
        if(t.tag==="Trans")return node(t.tag,dim,[family,node("Tube",formula(1,t.face,dims),[base,0]),base]);
        let tubes=0;
        for(const p of [...t.system].reverse())tubes=node("Tube",formula(1,p.face,dims),[encode(p.term,inner),tubes]);
        return node(t.tag,dim,[family,tubes,base]);
      }
      case "Path":case "PLam":case "Comp":{
        const {dim,inner}=bindDimensions(t,dims),family=encode(t.family,inner);
        if(t.tag==="Path")return node(t.tag,dim,[family,child(t.left),child(t.right)]);
        if(t.tag==="PLam")return node(t.tag,dim,[family,encode(t.body,inner)]);
        let tubes=0;
        for(const p of [...t.system].reverse())tubes=node("Tube",formula(1,p.face,dims),[encode(p.term,inner),tubes]);
        return node(t.tag,dim,[family,tubes,child(t.base)]);
      }
      case "Pushout":return node(t.tag,0,[child(t.center),child(t.left),child(t.right),child(t.maps)]);
      case "PushLeft":case "PushRight":return node(t.tag,0,[child(t.as),child(t.value)]);
      case "PushPath":return node(t.tag,formula(0,t.arg,dims),[child(t.as),child(t.value)]);
      case "PushElim":return node(t.tag,0,[child(t.motive),child(t.left),child(t.right),child(t.bridge)]);
      case "PApp":return node(t.tag,formula(0,t.arg,dims),[child(t.path),0]);
      case "Abort":return node(t.tag,0,[child(t.as),child(t.impossible)]);
      case "Sup":return node(t.tag,0,[child(t.as),child(t.label),child(t.children)]);
      case "Sum":return node(t.tag,0,[child(t.left),child(t.right)]);
      case "Inl":case "Inr":return node(t.tag,0,[child(t.as),child(t.value)]);
      case "SumRec":return node(t.tag,0,[child(t.motive),child(t.left),child(t.right),child(t.value)]);
      case "UnitRec":return node(t.tag,0,[child(t.motive),child(t.point),child(t.value)]);
      case "Glue":{
        const base=child(t.base);let system=0;
        for(const p of [...t.system].reverse())system=node("GlueSystem",formula(1,p.face,dims),[child(p.type),child(p.equiv),system]);
        return node(t.tag,0,[base,system]);
      }
      case "GlueTerm":{
        const as=child(t.as),base=child(t.base);let system=0;
        for(const p of [...t.system].reverse())system=node("Tube",formula(1,p.face,dims),[child(p.term),system]);
        return node(t.tag,0,[as,base,system]);
      }
      case "Unglue":return node(t.tag,0,[child(t.as),child(t.value)]);
      case "WRec":return node(t.tag,0,[child(t.motive),child(t.step),child(t.value)]);
      default:throw Error(`Unsupported native term ${t.tag}`);
    }
  };
  const hintLine=names=>`H ${names.length} ${names.map(n=>{
    if(!references.has(n))throw Error(`Unknown unfolding hint ${n}`);return references.get(n);
  }).join(" ")}`;
  for(const definition of definitions){
    const symbol=name(definition.name),body=encode(definition.value),type=definition.type?encode(definition.type):0;
    if(definition.unfoldingHints)lines.push(hintLine(definition.unfoldingHints));
    lines.push(`D ${symbol} ${body} ${type}`);
    references.set(definition.name,++terms);
    if(definition.unfoldingHints)lines.push(hintLine([]));
  }
  for(const [n,type]of assumptions){const symbol=name(n),handle=encode(type);lines.push(`A ${symbol} ${handle}`);}
  if(unfoldingHints.length)lines.push(hintLine(unfoldingHints));
  const value=encode(term),type=expected?encode(expected):0;lines.push(`Q ${value} ${type} ${normalize?1:0}`);
  const decode=t=>{
    if(!t||typeof t!=="object")return t;
    if(Array.isArray(t))return t.map(decode);
    const result=Object.fromEntries(Object.entries(t).map(([key,value])=>[key,decode(value)]));
    if(result.name?.startsWith("v")){const id=Number(result.name.slice(1));result.name=reverse.get(id)??`native${id}`;}
    return result;
  };
  return {input:lines.join("\n")+"\n",decode};
}

export function checkNative(term,expected=null,assumptions=[],{build=process.env.CUBICAL_NATIVE_BUILD??"build",normalize=true,definitions=[],unfoldingHints=[]}={}) {
  if(!["build","build-ubsan","build-sanitize"].includes(build))throw Error("Unknown native build.");
  const {input,decode}=nativeRequest(term,expected,assumptions,{normalize,definitions,unfoldingHints});
  const run=spawnSync(`${nativeRoot}${build}/kernel-cli`,[],{input,encoding:"utf8",maxBuffer:32*1024*1024,timeout:20000,killSignal:"SIGKILL"});
  if(run.status!==0)throw Error(`Native checker process failed (${run.status}): ${run.stderr}`);
  return decode(JSON.parse(run.stdout));
}
