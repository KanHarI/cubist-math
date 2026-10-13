// Selected source entry points contain immutable descriptions, never a live
// Scope or native handle. Execution is reconstructed by full-prefix replay.
// The nominal frontend bridge is explicit here while retained families move
// to the identity representation in CB2/CB3; it does not resolve moved syntax.
import {BindingTable,BindingAdapter,LexicalContext,bindingResolution,sourceOrigin} from "../cubist/bindings.mjs";
import {isTerm} from "./core.mjs";
import {snapshotSyntax} from "./syntax-graph.mjs";

const publicName=/^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/;
const RECURSIVE="\u0000recursive",SELECTION="\u0000selection";
const freeze=value=>{
  if(value&&typeof value==="object"&&!Object.isFrozen(value)) {
    Object.values(value).forEach(freeze);Object.freeze(value);
  }
  return value;
};

function recursiveDescription(value) {
  if(!value)return null;
  // Source syntax and checked core values are inert. Omit the site object
  // and parameter tokens; their occurrence is represented by owner/path.
  return Object.fromEntries(["source","key","params","labels","implicit","section","index","matched","generalizable","generalized","dependent",
    "fixed","state","bindings","results","destructed"].filter(key=>value[key]!==undefined)
    .map(key=>[key,value[key] instanceof Map?[...value[key]]:value[key]]));
}
function describedValue(value) {
  if(isTerm(value))return value;
  if(value?.tag==="Dimension")return {tag:value.tag,name:value.name,...(value.endpoint===undefined?{}:{endpoint:value.endpoint})};
  if(value?.tag==="Inductive")return {tag:value.tag,binding:value.binding};
  if(value?.tag==="InductiveConstructor")return {tag:value.tag,binding:value.inductive.binding,index:value.index};
  if(value?.tag==="Untranslated")return {tag:value.tag,binding:value.binding,reason:value.reason??value.message??null};
  // Permissions are mutable while the declaration is elaborated. Capture
  // them separately at each point; this part describes only the binding.
  if(value?.tag==="Recursive")return {tag:value.tag,source:value.source};
  throw new TypeError(`Scope value has no persistent description: ${value?.tag??typeof value}`);
}
const declaredIdentity=value=>value?.tag==="DefRef"?value.name
  :value?.tag==="InductiveConstructor"?`${value.inductive.binding}:constructor:${value.index}`:value?.binding;

export class ScopePoints {
  #owners=new Map();
  #occurrences=new Map();
  #origins=new Map();
  #available=new Map();
  #parents=[];
  #environments=new WeakMap();
  #contexts=new WeakMap();
  #dimensions=new WeakMap();
  constructor(revision,{onPoint=()=>{},probe=null,target=null}={}) {
    this.revision=revision;
    this.table=new BindingTable(revision);
    this.onPoint=onPoint;this.probe=probe;
    this.target=target;
  }
  owner(module) {
    const index=this.#owners.get(module)??0;
    this.#owners.set(module,index+1);
    return Object.freeze(["module",module,"declaration",String(index)]);
  }
  declaration(module,declaration,binding) {
    // A rejected duplicate cannot replace the origin of the declaration
    // whose value remains in the environment, even before its first use.
    if(this.#origins.has(binding))return;
    const origin=at=>sourceOrigin({revision:this.revision,module,start:at.start,end:at.end});
    const register=(key,token)=>{
      if(!this.#origins.has(key))this.#origins.set(key,{label:token.text,origin:origin(token),generated:!!declaration.generated});
    };
    register(binding,declaration.name);
    if(declaration.name.bindingId)this.#available.set(binding,this.table.get(declaration.name.bindingId));
    for(const [index,constructor] of (declaration.constructors??[]).entries()) {
      register(`${binding}:constructor:${index}`,constructor.name);
      register(`${module}__${constructor.name.text}`,constructor.name); // A refused constructor's source identity.
    }
  }
  bind(node,scope,role="local") {
    if(node.bindingId)return this.table.get(node.bindingId);
    const {unit}=scope;
    if(!unit.contextOwner||!Number.isInteger(node.start)||!Number.isInteger(node.end))return null;
    return this.table.allocate([...unit.contextOwner,"locals"],{role,label:node.label??node.text??node.name,
      origin:node.origin??sourceOrigin({revision:this.revision,module:unit.moduleName,start:node.start,end:node.end})});
  }
  #global(label,value,scope) {
    const identity=declaredIdentity(value);
    // Recursive placeholders are available only with their live structural
    // permissions. They are never materialized as checked global bodies.
    const key=identity??(value?.tag==="Recursive"?`${scope.unit.moduleName}__${value.source}`:null);
    if(!key)throw new TypeError(`Scope entry has no declaration identity: ${label}`);
    if(this.#available.has(key))return this.#available.get(key);
    const declared=this.#origins.get(key);
    if(!declared)throw new TypeError(`Scope entry has no source origin: ${label}`);
    const record=this.table.allocate(["available",key],{role:"declaration",label:declared.label,origin:declared.origin});
    this.#available.set(key,record);
    return record;
  }
  // Reconstruct an immutable lexical description and a separate live ID to
  // value mapping. Only the description is stored; the mapping is used by the
  // synchronous query callback and cannot leave its isolated session.
  bindings(scope) {
    let lexical=new LexicalContext();
    const values=new Map(),records=[],recursive=[];
    for(const [key,value] of scope.env) {
      const local=scope.sourceBindings.get(key),identified=scope.unit.bindingAdapter?.bindingForKey(key);
      if(!local&&!identified&&!publicName.test(key))continue;
      const record=local??identified??this.#global(key,value,scope),label=local?.label??identified?.label??key;
      lexical=lexical.bind(label,bindingResolution(record.id));
      values.set(record.id,value);
      records.push({label,id:record.id,origin:record.origin,role:record.role,value:describedValue(value)});
      if(value?.tag==="Recursive")recursive.push([key,record.id]);
    }
    return {lexical,values,records,recursive};
  }
  #environment(scope) {
    // Scope operations copy their maps. The module's top-level environment
    // changes between declarations, so its owner is part of this copy cache.
    // The cache contains only inert descriptions; no live values or Scope.
    let owners=this.#environments.get(scope.env);
    if(!owners)this.#environments.set(scope.env,owners=new WeakMap());
    const owner=scope.unit.contextOwner;
    if(!owners.has(owner)) {
      const live=this.bindings(scope);
      owners.set(owner,freeze({lexical:live.lexical.snapshot(),bindings:snapshotSyntax(live.records),recursive:live.recursive}));
    }
    return owners.get(owner);
  }
  #mapDescription(cache,map) {
    if(!cache.has(map))cache.set(map,snapshotSyntax([...map]));
    return cache.get(map);
  }
  #inside(id,body) {
    this.#parents.push(id);
    try {return body();}finally {this.#parents.pop();}
  }
  around(translator,node,scope,{phase="expression",goal=null,expected=null}={},body) {
    const {unit}=scope;
    // Quiet speculation creates no user-selectable instances. Its work is
    // still charged normally, and all earlier attempts replay in order.
    if(!unit.contextOwner||!Number.isInteger(node?.start)||!Number.isInteger(node?.end)
      ||!unit.observations.enabled("scope",this.onPoint))return body();
    const path=unit.observations.path,owner=unit.contextOwner;
    const counter=JSON.stringify([owner,path]),occurrence=this.#occurrences.get(counter)??0;
    this.#occurrences.set(counter,occurrence+1);
    const id=JSON.stringify([this.revision,owner,path,occurrence,phase]);
    // Replay still performs every declaration, attempt and scope transition.
    // Only the requested description needs materialization. Identity owners
    // and declaration labels are independent of observing earlier points.
    if(this.target&&id!==this.target)return this.#inside(id,body);
    const origin=node.origin??sourceOrigin({revision:this.revision,module:unit.moduleName,start:node.start,end:node.end});
    const basic={id,revision:this.revision,owner,attempt:path,occurrence,phase,origin,parent:this.#parents.at(-1)??null,
      declaration:unit.declaring};
    let description,live;
    try {
      const declaration=this.#origins.get(`${unit.moduleName}__${unit.declaring}`);
      if(declaration?.generated||scope.env.get(SELECTION))throw new TypeError("This generated or selected scope awaits its binding-family migration.");
      const environment=this.#environment(scope);
      description=freeze({...basic,available:true,lexical:environment.lexical,
        state:{format:"cubist-scope-state-1",bindings:environment.bindings,
          context:this.#mapDescription(this.#contexts,scope.context),dimensions:this.#mapDescription(this.#dimensions,scope.dimensions),
          slots:scope.slotOutcomes.snapshot(),recursion:snapshotSyntax({active:recursiveDescription(scope.env.get(RECURSIVE)),
            bindings:environment.recursive.map(([key,id])=>[id,recursiveDescription(scope.env.get(key))])}),
          goal:snapshotSyntax(goal),expected:snapshotSyntax(expected),
          rules:snapshotSyntax(Object.fromEntries(Object.entries(unit.simpRegistry??{}).map(([kind,entries])=>[kind,[...entries]])))}});
      if(this.probe)live=this.bindings(scope);
    } catch(error) {
      // A description failure never changes which source declarations check.
      // It marks this exact entry unavailable, without choosing another one.
      description=freeze({...basic,available:false,reason:error.message});
    }
    return this.#inside(id,()=>{
      // Probe before the body, while this exact native context is live. A
      // probe is private to replay and validates against the selected registry.
      this.probe?.(description,{translator,scope,goal,expected,...(live??{})});
      unit.observations.recordTo("scope",this.onPoint,description);
      return body();
    });
  }
  adapter(reserved=[]) {return new BindingAdapter(this.table,{reserved});}
}
