// A display adapter for retained syntax. It assigns labels to exact IDs;
// it never reads an elaboration environment or resolves a source spelling.
import {scopeMapped,scopesOf,binderName} from "./scopes.mjs";
import {mapResolution} from "./bindings.mjs";
import {parameterLambdas} from "./telescopes.mjs";
import {sourceText} from "../cubical-source-text.mjs";
import {substituteTerm,freeNames,T} from "../translator/core.mjs";
import {visitSyntax,mapSyntax} from "../translator/syntax-graph.mjs";

export function bindingDisplay(declaration,{table,globals=new Map(),locals=new Map()}={}) {
  const labels=new Map(),publicLabels=new Map(),taken=new Set(),used=new Set(),displays=new Map(),annotations=[];
  const opening=Symbol("model opening");
  const globalLabels=new Map();
  for(const [id,global] of globals) {
    if(!globalLabels.has(global.name))globalLabels.set(global.name,new Set());
    globalLabels.get(global.name).add(id);
  }
  let visits=0;
  const tick=()=>{if(++visits>50000)throw new RangeError("generated syntax exceeds the display budget");};
  for(const owner of [declaration,...declaration.constructors??[]])for(const p of owner.params??[])
    publicLabels.set(p.name.bindingId,p.label??p.name.label??p.name.text);
  // The same public parameter metadata is retained when inference wraps
  // the declaration's value in lambdas instead of checking an annotation.
  const tree=declaration.bindings?.inferred?{...declaration,params:[],
    value:parameterLambdas(declaration.params,declaration.value)}:declaration;
  const tokens=new Map();
  const scan=tree=>scopeMapped(tree,{deferred:true,enter(node) {
    tick();
    if(node.kind==="bindingReference")mapResolution(node.resolution,id=>{used.add(id);return id;},value=>{
      if(value.tag==="reserved")taken.add(value.label);return value;
    });
    if(node.kind==="instantiated")visitSyntax(node.value,value=>{if(typeof value?.name==="string")taken.add(value.name);});
    if(node.kind==="bindingReference")for(const [,replacement] of node.substitutions??[])scan(replacement);
    return node;
  },bind(token) {if(token.bindingId)tokens.set(token.bindingId,token);return token;},extend:at=>at},null);
  scan(tree);
  for(const id of used)if(globals.has(id))taken.add(globals.get(id).name.split(".")[0]);
  const reserved=new Set(taken);
  for(const [id,token] of tokens) {
    const label=publicLabels.get(id)??token.label??binderName(token);
    if(publicLabels.has(id)||token.bindingRole==="pattern") {labels.set(id,label);taken.add(label);continue;}
    if(label==="_"&&!used.has(id)) {labels.set(id,label);continue;}
  }
  // Labels belong to scopes. Disjoint scopes can reuse a label; formatting
  // placeholders, on the other hand, must avoid every raw token in the graph.
  visitSyntax(tree,value=>{if(typeof value==="string")taken.add(value);});
  const choose=(token,node,at,scope)=>{
    const id=token.bindingId,label=token.label??binderName(token);
    if(labels.has(id))return;
    // Several scopes of one node can overlap, while bind() sees their common
    // outer context. Reserve their chosen labels through the shared schema.
    const binders=node.kind?scopesOf(node,{deferred:true}).flatMap(scope=>scope.binders):scope.binders;
    const siblings=new Set(binders.filter(other=>other!==token).map(other=>labels.get(other.bindingId)));
    const stem=/^[A-Za-z_][A-Za-z_0-9]*$/.test(label)&&label!=="_"?label:"value";
    let chosen=stem,index=0;
    while(reserved.has(chosen)||at.has(chosen)||siblings.has(chosen))chosen=`${stem}${++index}`;
    taken.add(chosen);labels.set(id,chosen);
    if(chosen!==label)annotations.push(`Display alias ${chosen} denotes local binder ${label}.`);
  };
  const markers=new Map();
  const marker=(key,label,reason)=>{
    if(!markers.has(key)) {
      const text=`${label}⟦${markers.size+1}⟧`;
      markers.set(key,text);annotations.push(`${text}: ${reason}.`);
    }
    return markers.get(key);
  };
  const display=(text,{id,binding}={})=>{
    let key=`z${displays.size.toString(36)}`;
    while(taken.has(key))key+="_";
    taken.add(key);displays.set(key,{text,...(id?{bindingId:id}:{}),...(binding?{binding}:{})});return key;
  };
  const localName=id=>{
    const label=labels.get(id);
    return label==="_"&&used.has(id)?marker(id,label,"anonymous parameter; the marker names its identity, not a named-call label"):label;
  };
  const identity=(id,at)=>{
    const global=globals.get(id),label=labels.get(id)??global?.name??table.get(id).label;
    if(["notation","activation"].includes(table.get(id).role))
      return display(marker(id,table.get(id).label,"captured notation context supplied by the retained recipe"),{id});
    if(labels.has(id)&&at.get(label)===id)
      return display(at.get(opening)?.has(id)?marker(id,label,"captured local predates the model opening"):localName(id),{id,binding:locals.get(id)});
    if(global) {
      const collision=globalLabels.get(global.name).size>1||at.has(global.name.split(".")[0])||at.has(opening);
      return display(collision?marker(id,global.name,`captured declaration from ${global.module}`):global.name,
        {id,binding:global.binding});
    }
    return display(marker(id,label,labels.has(id)?"reference to an outer binder hidden by another binder"
      :"captured identity has no source-expressible declaration"),{id,binding:locals.get(id)});
  };
  const nominal=name=>({kind:"name",name});
  const coreIds=new Map([...globals].flatMap(([id,global])=>(global.keys??[]).map(key=>[key,id])));
  // Initial/free headers can contain checked, solved arguments abstracted
  // over the request parameters. Reuse the core printer only after replacing
  // every global and argument with an identity placeholder. Unsupported core
  // forms remain explicitly annotated, rather than invoking nominal lookup.
  const instantiated=(node,at,descend)=>{
    let value=node.value;
    const argumentsShown=new Set();
    for(const arg of node.args) {
      const displayed=descend(arg,at);
      if(displayed.kind!=="name"||!["Lam","LLam"].includes(value.tag))throw new TypeError("invalid retained header argument");
      argumentsShown.add(displayed.name);
      value=substituteTerm(value.body,value.name,T.variable(displayed.name));
    }
    const symbols={},names=new Map(),binders=new Set(),references=new Set(),updates=[];
    let unsupported=false;
    const marked=()=>nominal(display(marker(node,"checked","checked header argument without a faithful source form; inspect its declaration for the checked term")));
    const allowed=new Set(["Var","DefRef","U","Unit","Void","Point","Pi","Lam","LPi","LLam","LBound","App","LApp","Pair","Sigma","Sum","Fst","Snd","Sort","Con","LConst","LSucc","LMax"]);
    const declared=key=>{
      const id=coreIds.get(key);
      if(!id) {unsupported=true;return key;}
      if(!names.has(key)) {
        const text=identity(id,at);
        references.add(displays.get(text).text.split(".")[0]);
        names.set(key,text);symbols[text]={...globals.get(id).printing,name:text};
      }
      return names.get(key);
    };
    value=mapSyntax(value,()=>undefined);
    visitSyntax(value,term=>{
      if(!term||typeof term!=="object")return;
      if(term.tag&&!allowed.has(term.tag))unsupported=true;
      if(["Pi","Lam","Sigma","LPi","LLam"].includes(term.tag))binders.add(term.name);
      const intrinsic={Unit:"Unit",Void:"Void",Point:"tt"}[term.tag];
      if(intrinsic)references.add(intrinsic);
      if(intrinsic&&at.has(intrinsic))unsupported=true;
      if(term.tag==="DefRef")updates.push([term,"name",declared(term.name)]);
      if(term.tag==="Sort")updates.push([term,"signature",declared(term.signature)]);
      if(term.tag==="Con")updates.push([term,"name",declared(`${term.sort?.signature}:constructor:${term.index}`)]);
    });
    if(unsupported)return marked();
    // Read every original key before changing any shared node in the DAG.
    for(const [term,key,label] of updates)term[key]=label;
    for(const key of freeNames(value)) {
      if(argumentsShown.has(key)) {references.add(displays.get(key).text.split(".")[0]);continue;}
      if(!coreIds.has(key))return marked();
      value=substituteTerm(value,key,T.variable(declared(key)));
    }
    if([...binders].some(name=>references.has(name)||!/^[_A-Za-z][_A-Za-z0-9]*$/.test(name)))return marked();
    const text=sourceText(value,symbols,10000);
    if(text.includes("…")||text.includes("\u0000"))return marked();
    return {kind:"displaySource",text};
  };
  const reference=(node,at,descend,value=node.resolution)=>{
    tick();
    const again=resolution=>reference(node,at,descend,resolution);
    switch(value.tag) {
      case "binding": {
        const replacement=node.substitutions?.find(([id])=>id===value.id)?.[1];
        return replacement?descend(replacement,at):nominal(identity(value.id,at));
      }
      case "reserved": return nominal(display(at.has(value.label)||at.has(opening)
        ?marker(`reserved:${value.label}`,value.label,"reserved language reference retained across a binder or model opening"):value.label));
      case "member": return value.fields.reduce((receiver,field)=>({kind:"member",value:receiver,field:{text:field}}),again(value.receiver));
      case "slot": return (value.fields??[]).reduce((receiver,field)=>({kind:"member",value:receiver,field:{text:field}}),
        nominal(display(marker(value.id,table.get(value.id).label,"deferred constructor-or-variable pattern"),
          {id:value.id,binding:locals.get(value.id)})));
      case "application": return {kind:"call",fn:again(value.fn),args:value.args.map(again)};
      case "projected": return {kind:"call",fn:nominal(identity(value.projection,at)),args:[nominal(identity(value.receiver,at))]};
      default: return nominal(display(marker(value,node.spelling??value.label??value.tag,
        value.tag==="failure"?value.message:`retained ${value.tag} interpretation; no destination-name lookup`)));
    }
  };
  const rendered=scopeMapped(tree,{deferred:true,
    enter(node,at,descend) {
      tick();
      if(node.kind==="bindingReference")return reference(node,at,descend);
      if(node.kind==="instantiated")return instantiated(node,at,descend);
      if(node.kind==="number"&&(node.notationSelection||node.literalFailure))
        return nominal(display(marker(node,node.text??String(node.value),node.literalFailure?.message
          ??"numeric token retains its notation context; term or interval use is determined during elaboration")));
      if(node.kind==="operandAlternatives"||node.kind==="notationReceiver")
        return nominal(display(marker(node,node.origin?"operand":node.kind,"retained term/receiver interpretation is selected during elaboration")));
      if(node.kind==="name"&&node.name!=="_")throw new TypeError("unresolved nominal generated reference");
      return node;
    },
    bind(token,node,scope,at) {
      if(!token.bindingId)throw new TypeError("generated binder has no identity");
      choose(token,node,at,scope);
      const id=token.bindingId,text=token.bindingRole==="pattern"&&binderName(token)!=="_"
        ?marker(id,binderName(token),"deferred constructor-or-variable pattern"):localName(id);
      return {...token,text:display(text,{id,binding:locals.get(id)}),displayLabel:labels.get(id)};
    },
    extend(at,binders,_node,scope) {
      at=new Map(at);
      if(scope.role==="activation"&&scope.effects.labels)at.set(opening,new Set([...at.values()].filter(value=>typeof value==="string")));
      for(const token of binders)if(!["notation","activation"].includes(token.bindingRole))at.set(token.displayLabel,token.bindingId);
      return at;
    },
  },new Map());
  const declarationName=token=>display(token.text,{id:token.bindingId,binding:globals.get(token.bindingId)?.binding});
  return {tree:rendered,displays,annotations,declarationName};
}
