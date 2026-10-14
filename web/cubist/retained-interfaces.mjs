// Ordered source entry for complete declaration interfaces. Header domains,
// member parameter domains, result and body are resolved together, once.
// Subsequent consumers transform the retained syntax through ID maps; they
// never rebuild its lexical scope from the eventual list of field labels.
import {bindingResolution,sourceOrigin,expandedOrigin} from "./bindings.mjs";
import {resolveBindingSyntax,cloneBindingSyntax,remapBindingSyntax,bindingSyntaxView,sameBindingSyntax} from "./binding-syntax.mjs";
import {parameterForalls} from "./telescopes.mjs";

const retainedKeys=new Set(["kind","name","params","type","value","body","valueParameters","universe","level",
  "notation","uses","computable","keyword","levelToken","start","end","origin","typedValue","valueStart","valueEnd","modifierStart","implicitParameters"]);
function interfaceTree(item) {
  for(const key of Object.keys(item))if(!retainedKeys.has(key))
    throw new TypeError(`Unmodelled retained interface property: ${key}`);
  if(item.notation||item.uses?.length)
    throw new TypeError("Binding syntax family has not migrated: interface notation or use");
  if(item.universe&&(item.kind!=="sort"||item.type))
    throw new TypeError("A carrier universe must be its one retained result type.");
  const type=item.universe?{kind:"name",name:item.universe.text,...item.universe}:item.type??null;
  return {kind:"def",name:item.name,params:item.params??[],type,
    ...(item.computable?{computable:true}:{}),
    ...(item.valueParameters?{valueParameters:item.valueParameters}:{}),
    ...(item.value===undefined?{}:{value:item.value}),...(item.body===undefined?{}:{body:item.body})};
}

// A view of the same complete interface for type-purpose consumers. It
// retains the entire ordered telescope; it is never resolved a second time.
export function interfaceSignature(entry) {
  const {name,value,body,...tree}=entry.syntax.tree;
  return bindingSyntaxView(entry.syntax,tree);
}

// A type-purpose view closes the same parameter IDs with their retained
// groups. It allocates nothing and never recovers groups from equal domains.
export function interfaceType(entry) {
  const {params,type}=entry.syntax.tree;
  if(!type)throw new TypeError("An inferred interface needs its checked result type before type analysis.");
  return bindingSyntaxView(entry.syntax,parameterForalls(params,type));
}

export class RetainedInterfaces {
  #next=0;
  constructor({table,owner,context,source,constructors=[],
    evidenceTypes=new Map(["IsSet","IsProp"].map(label=>[label,context.lookup(label)]))}) {
    Object.assign(this,{table,owner,context,source,constructors,evidenceTypes});
    this.entries=[];this.header=null;
  }
  #resolve(tree,owner,{context=this.context,self=null}={}) {
    return resolveBindingSyntax(tree,{table:this.table,owner,context,source:this.source,constructors:this.constructors,
      evidenceTypes:this.evidenceTypes,self});
  }
  parameters(name,params) {
    if(this.header||this.entries.length)throw new TypeError("A retained header precedes its members and is resolved once.");
    name={...name,origin:name.origin??sourceOrigin({...this.source,start:name.start,end:name.end})};
    const syntax=this.#resolve({kind:"def",name,params,type:null,value:null},[...this.owner,"header"]);
    for(const parameter of syntax.tree.params)if(parameter.name.bindingId)
      this.context=this.context.bind(parameter.name.text,bindingResolution(parameter.name.bindingId));
    this.header=syntax;
    return syntax;
  }
  retain(item,{kind=item.kind,self=false}={}) {
    const tree=interfaceTree(item);
    const owner=[...this.owner,"member",String(this.#next++)];
    const binding=this.table.allocate(owner,{role:kind==="derived"?"helper":"field",label:item.name.text,
      origin:item.name.origin??sourceOrigin({...this.source,start:item.name.start,end:item.name.end})});
    const context=this.context;
    const syntax=this.#resolve(tree,[...owner,"telescope"],{context,self:self?binding:null});
    const entry=Object.freeze({id:binding.id,label:binding.label,kind,binding,syntax,recursive:self,lexical:context.snapshot(),
      interface:Object.freeze(this.#interface()),
      ...(kind==="sort"?{level:item.level??null}:{})});
    this.entries.push(entry);
    this.context=this.context.bind(binding.label,bindingResolution(binding.id));
    return entry;
  }
  #interface() {
    return [...(this.header?.tree.params??[]).flatMap(p=>p.name.bindingId?[p.name.bindingId]:[]),
      ...this.entries.map(entry=>entry.id)];
  }
  #mapped(entry,correspondence,syntax=entry.syntax) {
    for(const id of entry.interface)if(!correspondence.has(id))
      throw new TypeError(`An inherited interface is missing a correspondence for ${this.table.get(id).label}.`);
    return remapBindingSyntax(syntax,this.table,correspondence);
  }
  // Inheritance supplies the actual parent-to-child open-interface map.
  // Each member's own telescope gets fresh locals, preserving its authored
  // origins. Public renaming affects only the new field's label.
  inherit(entry,correspondence,{label=entry.label,site}={}) {
    this.#mapped(entry,correspondence);
    const owner=[...this.owner,"member",String(this.#next++)];
    const expansion=site?{kind:"inheritance",site:sourceOrigin(site)}:undefined;
    const origin=expansion?expandedOrigin(entry.binding.origin,expansion):entry.binding.origin;
    const assigned=correspondence.get(entry.id);
    const binding=assigned?this.table.get(assigned):this.table.allocate(owner,
      {role:entry.binding.role,label,origin,original:entry.binding.original??entry.id});
    if(binding.label!==label||binding.role!==entry.binding.role)
      throw new TypeError("An inherited member's binding disagrees with its interface.");
    if(this.entries.some(existing=>existing.id===binding.id))
      throw new TypeError("A shared inherited binding must be compared before it is admitted once.");
    const map=new Map(correspondence).set(entry.id,binding.id);
    const cloned=cloneBindingSyntax(entry.syntax,this.table,[...owner,"telescope"],{expansion});
    const syntax=remapBindingSyntax(cloned.syntax,this.table,map);
    const resolution=value=>value.tag==="binding"?{...value,id:map.get(value.id)??value.id}
      :value.tag==="slot"?{...value,id:map.get(value.id)??value.id,enclosing:resolution(value.enclosing)}:value;
    const inherited=Object.freeze({...entry,id:binding.id,label,binding,syntax,
      interface:Object.freeze(this.#interface()),
      lexical:Object.freeze(entry.lexical.map(([label,value])=>Object.freeze([label,Object.freeze(resolution(value))])))});
    this.entries.push(inherited);this.context=this.context.bind(label,bindingResolution(binding.id));
    correspondence.set(entry.id,binding.id);
    return inherited;
  }
  // Sharing is an explicit multi-parent admission. Compare instantiated
  // signatures before allocating the one child identity, then map every
  // parent occurrence to it. Fresh local clone IDs cannot affect this test.
  inheritShared(candidates,{label=candidates[0]?.entry.label,site}={}) {
    if(!candidates.length)throw new TypeError("An inherited field needs a parent candidate.");
    const first=candidates[0],origin=entry=>entry.binding.original??entry.id;
    const assigned=new Set(candidates.map(({entry,correspondence})=>correspondence.get(entry.id)).filter(Boolean));
    if(assigned.size>1)throw new TypeError("Shared parent fields have conflicting child identities.");
    const signature=({entry,correspondence})=>{
      // A helper has a value as well as a type. The same ancestor's helper
      // can compute differently under two field maps even when its result
      // type is unchanged. Compare its body too, aligning structural self.
      const {name,...tree}=entry.syntax.tree;
      const syntax=entry.kind==="derived"?bindingSyntaxView(entry.syntax,tree):interfaceSignature(entry);
      const map=new Map(correspondence).set(entry.id,[...assigned][0]??first.entry.id);
      return this.#mapped(entry,map,syntax);
    };
    const expected=signature(first);
    for(const candidate of candidates.slice(1)) {
      const a=first.entry,b=candidate.entry;
      const commonOrigin=origin(a)===origin(b);
      const independentCarrier=["sort","evidence"].includes(a.kind);
      if(a.kind!==b.kind||!commonOrigin&&!independentCarrier||a.level!==b.level
        ||!sameBindingSyntax(expected,signature(candidate)))
        throw new TypeError(`Inherited interfaces for ${label} have different origins, kinds or instantiated types.`);
    }
    const map=new Map(first.correspondence);
    if(assigned.size)map.set(first.entry.id,[...assigned][0]);
    const inherited=this.inherit(first.entry,map,{label,site});
    for(const {entry,correspondence} of candidates)correspondence.set(entry.id,inherited.id);
    return inherited;
  }
}
