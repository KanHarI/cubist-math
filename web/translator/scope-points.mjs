// Selected source entry points contain immutable descriptions, never a live
// Scope or native handle. Execution is reconstructed by full-prefix replay.
import {BindingAdapter,LexicalContext,bindingResolution,sourceOrigin,mapResolution} from "../cubist/bindings.mjs";
import {CompilationBindings} from "./compilation-bindings.mjs";
import {isTerm} from "./core.mjs";
import {snapshotSyntax} from "./syntax-graph.mjs";
import {expandedSource} from "../cubist/source-syntax.mjs";
import {sourceNotationInventory} from "./binding-module.mjs";
import {notationContextKey} from "./notation-context.mjs";

const publicName=/^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/;
const RECURSIVE="\u0000recursive";
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
  if(value?.tag==="Notation"&&value.bindingId)return {tag:value.tag,bindingId:value.bindingId,modelBinding:value.modelBinding??null};
  // Permissions are mutable while the declaration is elaborated. Capture
  // them separately at each point; this part describes only the binding.
  if(value?.tag==="Recursive")return {tag:value.tag,source:value.source};
  throw new TypeError(`Scope value has no persistent description: ${value?.tag??typeof value}`);
}
export class ScopePoints {
  #owners=new Map();
  #occurrences=new Map();
  #parents=[];
  #environments=new WeakMap();
  #contexts=new WeakMap();
  #dimensions=new WeakMap();
  #rules=new WeakMap();
  constructor(revision,{onPoint=()=>{},probe=null,target=null,compilation=new CompilationBindings(revision)}={}) {
    if(compilation.revision!==revision)throw new TypeError("Scope collection binding revision mismatch.");
    this.revision=revision;
    this.compilation=compilation;this.table=compilation.table;
    this.onPoint=onPoint;this.probe=probe;
    this.target=target;
  }
  owner(module) {
    const index=this.#owners.get(module)??0;
    this.#owners.set(module,index+1);
    return Object.freeze(["module",module,"declaration",String(index)]);
  }
  expansion(tree,kind,node,unit) {
    const at=node.origin??sourceOrigin({revision:this.revision,module:unit.moduleName,start:node.start,end:node.end});
    return expandedSource(tree,{kind,site:at});
  }
  bind(node,scope,role="local") {
    if(node.bindingId)return this.table.get(node.bindingId);
    const {unit}=scope;
    if(!unit.contextOwner||!Number.isInteger(node.start)||!Number.isInteger(node.end))return null;
    return this.table.allocate([...unit.contextOwner,"locals"],{role,label:node.label??node.text??node.name,
      origin:node.origin??sourceOrigin({revision:this.revision,module:unit.moduleName,start:node.start,end:node.end})});
  }
  activation(node,scope) {
    const record=this.bind({...node,text:"selection"},scope,"activation");
    return record?{text:record.label,bindingId:record.id,bindingRole:record.role,
      origin:record.origin,start:node.start,end:node.end}:null;
  }
  selected(scope,activation,effects) {
    if(!scope.lexical||!activation)return scope;
    let lexical=scope.lexical;
    if(effects.labels)lexical=lexical.open(activation.bindingId);
    if(effects.notation)lexical=lexical.withSelectedNotation(activation.bindingId);
    return scope.with({lexical});
  }
  // Source globals come from the current declaration environment. Locals and
  // effects retain their actual introduction order; private keys supply values
  // only, so an outer capture cannot become visible merely by being stored.
  bindings(scope) {
    const inventory=sourceNotationInventory(this.compilation,scope.env),adapter=new BindingAdapter(this.table);
    let lexical=new LexicalContext().withNotations(inventory);
    const values=new Map(),keys=new Map(),records=new Map(),recursive=[],contexts=new Map();
    const add=(record,key,value)=>{
      values.set(record.id,value);keys.set(key,record.id);
      records.set(record.id,{label:record.label,id:record.id,origin:record.origin,role:record.role,value:describedValue(value)});
      if(value?.tag==="Recursive")recursive.push([key,record.id]);
    };
    for(const entry of inventory)if(entry.notation) {
      const record=this.table.get(entry.notation.id),key=adapter.key(record.id),value=scope.env.get(key);
      if(value?.bindingId!==record.id)throw new TypeError("A scope's named notation needs its exact receipt.");
      add(record,key,value);
    }
    for(const [key,value] of scope.env) {
      if(value?.tag==="Notation")continue;
      const local=scope.sourceBindings.get(key),identified=adapter.bindingForKey(key),named=publicName.test(key);
      if(!local&&!identified&&!named)continue;
      const record=local??identified??this.compilation.ofValue(value,scope.unit);
      if(!record) {
        // An opened member is described by its activation/projection, not by
        // inventing a declaration identity for the resulting core value.
        const resolved=scope.slotOutcomes.resolve(scope.lexical?.qualified(key).value);
        if(!resolved||resolved.tag==="missing")throw new TypeError(`Scope entry has no declaration identity: ${key}`);
        continue;
      }
      if(!local&&!identified)lexical=lexical.bind(key,bindingResolution(record.id));
      add(record,key,value);
    }
    lexical=new LexicalContext([...lexical.snapshot(),...scope.lexical?.snapshot()??[]]);
    const ids=new Set(values.keys());
    for(const [,resolution] of lexical.snapshot())mapResolution(resolution,id=>{ids.add(id);return id;});
    for(const id of ids) {
      const context=scope.env.get(notationContextKey(adapter.key(id)));
      if(context)contexts.set(id,context);
    }
    return {lexical,values,keys,records:[...records.values()],recursive,contexts};
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
      owners.set(owner,freeze({lexical:live.lexical.snapshot(),bindings:snapshotSyntax(live.records),
        sources:snapshotSyntax([...scope.localSources]),recursive:live.recursive,notations:[...live.contexts.keys()]}));
    }
    return owners.get(owner);
  }
  #mapDescription(cache,map) {
    if(!cache.has(map))cache.set(map,snapshotSyntax([...map]));
    return cache.get(map);
  }
  #ruleDescription(unit) {
    const registry=unit.simpRegistry;
    if(!registry)return snapshotSyntax({});
    // Registrations occur between declarations; a declaration/attempt may
    // read or copy its registry, never mutate its entries. The owner keeps a
    // later registration from reusing an earlier description.
    let owners=this.#rules.get(registry);
    if(!owners)this.#rules.set(registry,owners=new WeakMap());
    if(!owners.has(unit.contextOwner))owners.set(unit.contextOwner,
      snapshotSyntax(Object.fromEntries(Object.entries(registry).map(([kind,entries])=>[kind,[...entries]]))));
    return owners.get(unit.contextOwner);
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
      declaration:unit.declaring,declarationId:this.compilation.declaration(`${unit.moduleName}__${unit.declaring}`)?.binding.id??null};
    let description,live;
    try {
      if(unit.scopeUnavailable)throw new TypeError(unit.scopeUnavailable);
      const authored=origin.module===unit.moduleName?unit.source:unit.sources?.[origin.module];
      if(authored===undefined||origin.start<0||origin.end>authored.length)
        throw new TypeError("This scope has no matching authored source range.");
      const environment=this.#environment(scope);
      description=freeze({...basic,available:true,lexical:environment.lexical,
        state:{format:"cubist-scope-state-1",bindings:environment.bindings,sources:environment.sources,notations:environment.notations,
          context:this.#mapDescription(this.#contexts,scope.context),dimensions:this.#mapDescription(this.#dimensions,scope.dimensions),
          slots:scope.slotOutcomes.snapshot(),recursion:snapshotSyntax({active:recursiveDescription(scope.env.get(RECURSIVE)),
            bindings:environment.recursive.map(([key,id])=>[id,recursiveDescription(scope.env.get(key))])}),
          goal:snapshotSyntax(goal),expected:snapshotSyntax(expected),evidence:snapshotSyntax(scope.evidence),
          rules:this.#ruleDescription(unit)}});
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
}
