// Selected source entry points contain immutable descriptions, never a live
// Scope or native handle. Execution is reconstructed by full-prefix replay.
import {BindingAdapter,LexicalContext,sourceOrigin,mapResolution} from "../cubist/bindings.mjs";
import {CompilationBindings} from "./compilation-bindings.mjs";
import {isTerm} from "./core.mjs";
import {snapshotSyntax,mapSyntax,visitSyntax,syntaxGraphBudget} from "./syntax-graph.mjs";
import {sourceBindingInputs} from "./binding-module.mjs";
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
function describedValue(value,operand) {
  if(isTerm(value))return value;
  if(value?.tag==="Dimension")return {tag:value.tag,name:value.name,...(value.endpoint===undefined?{}:{endpoint:value.endpoint})};
  if(value?.tag==="Inductive")return {tag:value.tag,binding:value.binding};
  if(value?.tag==="InductiveSelf")return {tag:value.tag,binding:value.binding,sort:value.sort,slots:value.slots};
  if(value?.tag==="InductiveConstructor")return value.head
    ?{tag:value.tag,head:value.head,order:value.order,arity:value.arity,dims:value.dims}
    :{tag:value.tag,binding:value.inductive.binding,index:value.index};
  if(value?.tag==="Untranslated")return {tag:value.tag,binding:value.binding,reason:value.reason??value.message??null};
  if(value?.tag==="Notation"&&value.bindingId)return {tag:value.tag,bindingId:value.bindingId,modelBinding:value.modelBinding??null};
  // Permissions are mutable while the declaration is elaborated. Capture
  // them separately at each point; this part describes only the binding.
  if(value?.tag==="Recursive")return {tag:value.tag,source:value.source};
  if(value?.tag==="SourceOperand")return operand(value);
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
  #notations=new Map();
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
  sourceContext(env) {return sourceBindingInputs(this.compilation,env).context;}
  retainNotation(id,context) {this.#notations.set(id,context);}
  notationContext(id) {
    const context=this.#notations.get(id);
    if(!context)throw new TypeError("A notation scope has no retained source context.");
    return context;
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
  // Source entry supplies the complete lexical context. Runtime keys supply
  // values only; neither a caller's public names nor its private captures can
  // introduce visibility inside a retained notation body.
  bindings(scope,descriptions={copies:new WeakMap(),budget:syntaxGraphBudget()}) {
    const adapter=new BindingAdapter(this.table);
    const lexical=scope.lexical??new LexicalContext();
    const values=new Map(),keys=new Map(),records=new Map(),recursive=[],contexts=new Map();
    const add=(record,key,value)=>{
      values.set(record.id,value);keys.set(key,record.id);
      descriptions.budget.tick();
      records.set(record.id,{label:record.label,id:record.id,origin:record.origin,role:record.role,
        value:describedValue(value,value=>this.#operandDescription(value,descriptions))});
      if(value?.tag==="Recursive")recursive.push([key,record.id]);
    };
    for(const [key,value] of scope.env) {
      const local=scope.sourceBindings.get(key)?.binding,identified=adapter.bindingForKey(key),named=publicName.test(key);
      // Public notation labels may shadow a source notation. Its private
      // receipt remains available; only the lexical context grants visibility.
      if(value?.tag==="Notation") {
        if(!identified)continue;
        if(value.bindingId!==identified.id)throw new TypeError("A scope's named notation needs its exact receipt.");
      }
      if(!local&&!identified&&!named)continue;
      const record=local??identified??this.compilation.ofValue(value,scope.unit);
      if(!record) {
        // An opened member is described by its activation/projection, not by
        // inventing a declaration identity for the resulting core value.
        const resolved=scope.slotOutcomes.resolve(scope.lexical?.qualified(key).value);
        if(!resolved||resolved.tag==="missing")throw new TypeError(`Scope entry has no declaration identity: ${key}`);
        continue;
      }
      add(record,key,value);
    }
    const ids=new Set(values.keys());
    for(const [,resolution] of lexical.snapshot())mapResolution(resolution,id=>{ids.add(id);return id;});
    for(const id of ids) {
      const context=scope.env.get(notationContextKey(adapter.key(id)));
      if(context)contexts.set(id,context);
    }
    return {lexical,values,keys,records:[...records.values()],recursive,contexts};
  }
  #operandDescription(operand,descriptions) {
    const {copies,budget}=descriptions;
    if(copies.has(operand))return copies.get(operand);
    const result={tag:"SourceOperand"};copies.set(operand,result);
    const caller=scope=>{
      if(copies.has(scope))return copies.get(scope);
      budget.tick();
      const data={module:scope.unit.moduleName,owner:scope.unit.contextOwner};copies.set(scope,data);
      const live=this.bindings(scope,descriptions);
      return Object.assign(data,{lexical:live.lexical.snapshot(),bindings:live.records,sources:[...scope.localSources],
        context:[...scope.context],dimensions:[...scope.dimensions],evidence:scope.evidence,inheritedDefinitions:scope.inheritedDefinitions,
        slots:scope.slotOutcomes.snapshot(),notations:[...live.contexts.keys()],rules:this.#ruleDescription(scope.unit)});
    };
    const syntax=node=>mapSyntax(node,value=>value.kind==="scoped"
      ?{...value,node:syntax(value.node),scope:caller(value.scope)}:undefined,{budget});
    return Object.assign(result,{node:syntax(operand.node),caller:caller(operand.scope)});
  }
  #callerPermissions(scope) {
    // A lazy caller's recursion permissions can change without replacing its
    // environment. Snapshot them at this point, separately from shared values.
    // The ordered traversal corresponds to the retained operand/caller graph;
    // scopes exist only during this walk and never enter its returned data.
    const scopes=[scope],seen=new Set(scopes),budget=syntaxGraphBudget();
    const include=caller=>{if(!seen.has(caller)){seen.add(caller);scopes.push(caller);}};
    for(const caller of scopes)for(const value of caller.env.values()) {
      budget.tick();
      if(value?.tag!=="SourceOperand")continue;
      include(value.scope);
      visitSyntax(value.node,node=>{if(node?.kind==="scoped")include(node.scope);},
        {budget,children:node=>node.kind==="scoped"?[node.node]:Object.values(node)});
    }
    return scopes.slice(1).map(caller=>({module:caller.unit.moduleName,owner:caller.unit.contextOwner,
      active:recursiveDescription(caller.env.get(RECURSIVE)),
      bindings:[...caller.env].filter(([key,value])=>key!==RECURSIVE&&value?.tag==="Recursive")
        .map(([key,value])=>[key,recursiveDescription(value)])}));
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
      const description=freeze({lexical:live.lexical.snapshot(),bindings:snapshotSyntax(live.records),
        sources:snapshotSyntax([...scope.localSources]),recursive:live.recursive,notations:[...live.contexts.keys()]});
      owners.set(owner,description);
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
      declaration:unit.declaring?.name??null,
      declarationId:this.compilation.declaration(`${unit.moduleName}__${unit.declaring?.name}`)?.binding.id??null};
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
            bindings:environment.recursive.map(([key,id])=>[id,recursiveDescription(scope.env.get(key))]),
            callers:this.#callerPermissions(scope)}),
          goal:snapshotSyntax(goal),expected:snapshotSyntax(expected),evidence:snapshotSyntax(scope.evidence),
          inheritedDefinitions:snapshotSyntax(scope.inheritedDefinitions),
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
