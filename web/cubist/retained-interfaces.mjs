// Ordered source entry for complete declaration interfaces. Header domains,
// member parameter domains, result and body are resolved together, once.
// Subsequent consumers transform the retained syntax through ID maps; they
// never rebuild its lexical scope from the eventual list of field labels.
import {bindingResolution,reservedResolution,sourceOrigin,expandedOrigin} from "./bindings.mjs";
import {resolveBindingSyntax,cloneBindingSyntax,remapBindingSyntax,validateBindingCorrespondence,bindingSyntaxView,sameBindingSyntax,bindingUses} from "./binding-syntax.mjs";
import {parameterForalls} from "./telescopes.mjs";

const retainedKeys=new Set(["kind","name","params","type","value","body","valueParameters","universe","level",
  "notation","uses","computable","keyword","levelToken","start","end","origin","typedValue","valueStart","valueEnd","modifierStart","implicitParameters"]);
export const parentNamespaceFailure=(theory,{description,namespace,member})=>
  `${description}, ${theory}'s parent ${namespace}, has no field ${member}.`;
export class InheritedInterfaceConflict extends TypeError {
  constructor(label) {
    super(`Inherited interfaces for ${label} have different origins, kinds or instantiated types.`);
    this.name="InheritedInterfaceConflict";this.label=label;
  }
}
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
  #resolve(tree,owner,{context=this.context,self=null,fixedReferences=new Map(),notation=null}={}) {
    const universeReferences=new Map((this.header?.tree.params??[]).filter(p=>p.bound&&p.name.text!=="_")
      .map(p=>[p.name.text,bindingResolution(p.name.bindingId)]));
    // `set U` and `prop U` are universe positions fixed by the grammar.
    // Their meaning does not change under a term parameter or helper U.
    for(const parameter of tree.params??[])if(parameter.level&&parameter.type?.kind==="name") {
      const label=parameter.type.name;
      fixedReferences.set(parameter.type,/^U+[0-9]+$/.test(label)?reservedResolution(label):{tag:"universe",label});
    }
    return resolveBindingSyntax(tree,{table:this.table,owner,context,source:this.source,constructors:this.constructors,
      evidenceTypes:this.evidenceTypes,self,fixedReferences,universeReferences,namespaceBoundary:context,notation,
      namespaceFailure:error=>parentNamespaceFailure(this.header?.tree.name.text??tree.name.text,error)});
  }
  parameters(name,params,{fixedReferences=new Map()}={}) {
    if(this.header||this.entries.length)throw new TypeError("A retained header precedes its members and is resolved once.");
    name={...name,origin:name.origin??sourceOrigin({...this.source,start:name.start,end:name.end})};
    const syntax=this.#resolve({kind:"def",name,params,type:null,value:null},[...this.owner,"header"],{fixedReferences});
    for(const parameter of syntax.tree.params)if(parameter.name.bindingId&&parameter.name.text!=="_")
      this.context=this.context.bind(parameter.name.text,bindingResolution(parameter.name.bindingId));
    this.header=syntax;
    return syntax;
  }
  retain(item,{kind=item.kind,self=false,transform=syntax=>syntax,notation=null,ownNotation=null}={}) {
    const tree=interfaceTree(item);
    const fixedReferences=new Map();
    if(item.universe)fixedReferences.set(tree.type,{tag:"universe",label:item.universe.text});
    const owner=[...this.owner,"member",String(this.#next++)];
    const binding=this.table.allocate(owner,{role:kind==="derived"?"helper":"field",label:item.name.text,
      origin:item.name.origin??sourceOrigin({...this.source,start:item.name.start,end:item.name.end})});
    const context=this.context;
    // The declaration owns its operation before its body is resolved. The
    // rule's operands/receiver were prepared outside the formal parameters;
    // adding this ID does not publish a term name or grant availability.
    if(ownNotation)notation={...notation,bindings:{...notation?.bindings,
      [ownNotation.key]:{...ownNotation,field:binding.id}}};
    const syntax=transform(this.#resolve(tree,[...owner,"telescope"],{context,self:self?binding:null,fixedReferences,notation}));
    const recursive=self||kind==="derived"&&bindingUses(syntax,{conditional:true}).some(use=>use.id===binding.id);
    const entry=Object.freeze({id:binding.id,label:binding.label,kind,binding,syntax,recursive,
      interface:Object.freeze(this.#interface()),
      ...(kind==="sort"?{level:item.level??null}:{})});
    this.entries.push(entry);
    this.context=this.context.bind(binding.label,bindingResolution(binding.id));
    return entry;
  }
  // Carrier evidence is generated from the resolved carrier interface. Its
  // own telescope is cloned once; neither its predicate nor its family
  // application is read back as source text in the extended field scope.
  evidence(carrier) {
    if(!this.entries.includes(carrier)||carrier.kind!=="sort"||!["set","prop"].includes(carrier.level))
      throw new TypeError("Carrier evidence needs an admitted set or proposition interface.");
    const label=`${carrier.label}_is_${carrier.level}`,predicate=carrier.level==="set"?"IsSet":"IsProp";
    if(!this.evidenceTypes.has(predicate))throw new TypeError(`Carrier evidence needs a source resolution for ${predicate}.`);
    const owner=[...this.owner,"member",String(this.#next++)],origin=carrier.binding.origin;
    const binding=this.table.allocate(owner,{role:"field",label,origin});
    const ref=(resolution,spelling)=>({kind:"bindingReference",resolution,spelling,origin,start:origin.start,end:origin.end});
    const {params,type}=carrier.syntax.tree;
    let member=ref(bindingResolution(carrier.id),carrier.label);
    if(params.length)member={kind:"call",fn:member,args:params.map(p=>ref(bindingResolution(p.name.bindingId),p.name.text)),origin};
    const tree={kind:"def",name:{text:label,start:origin.start,end:origin.end,origin},params,
      type:{kind:"call",fn:ref(this.evidenceTypes.get(predicate),predicate),args:[type,member],origin}};
    const syntax=cloneBindingSyntax(bindingSyntaxView(carrier.syntax,tree),this.table,[...owner,"telescope"],
      {expansion:{kind:"generation",site:origin}}).syntax;
    const entry=Object.freeze({id:binding.id,label,kind:"evidence",binding,syntax,recursive:false,
      interface:Object.freeze(this.#interface()),of:carrier.id,evidence:predicate});
    this.entries.push(entry);this.context=this.context.bind(label,bindingResolution(binding.id));
    return entry;
  }
  #interface() {
    return [...(this.header?.tree.params??[]).flatMap(p=>p.name.bindingId?[p.name.bindingId]:[]),
      ...this.entries.map(entry=>entry.id)];
  }
  #requireCorrespondence(entry,correspondence) {
    for(const id of entry.interface)if(!correspondence.has(id))
      throw new TypeError(`An inherited interface is missing a correspondence for ${this.table.get(id).label}.`);
    validateBindingCorrespondence(entry.syntax,this.table,correspondence);
  }
  // Inheritance supplies the actual parent-to-child open-interface map.
  // Each member's own telescope gets fresh locals, preserving its authored
  // origins. Public renaming affects only the new field's label.
  inherit(entry,correspondence,{label=entry.label,site}={}) {
    this.#requireCorrespondence(entry,correspondence);
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
    // Only the canonical interface and its structural metadata inherit.
    // Analysis/checking views and generated projection IDs belong to the
    // parent's artifacts and must be rebuilt for the child correspondence.
    const metadata=Object.fromEntries(["kind","recursive","level","family","visible","evidence"]
      .filter(key=>Object.hasOwn(entry,key)).map(key=>[key,entry[key]]));
    const inherited=Object.freeze({...metadata,id:binding.id,label,binding,syntax,
      ...(entry.of?{of:map.get(entry.of)??entry.of}:{}),
      interface:Object.freeze(this.#interface())});
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
      this.#requireCorrespondence(entry,map);
      return remapBindingSyntax(syntax,this.table,map);
    };
    const expected=signature(first);
    for(const candidate of candidates.slice(1)) {
      const a=first.entry,b=candidate.entry;
      const commonOrigin=origin(a)===origin(b);
      const independentCarrier=["sort","evidence"].includes(a.kind);
      if(a.kind!==b.kind||!commonOrigin&&!independentCarrier||a.level!==b.level
        ||!sameBindingSyntax(expected,signature(candidate)))
        throw new InheritedInterfaceConflict(label);
    }
    const map=new Map(first.correspondence);
    if(assigned.size)map.set(first.entry.id,[...assigned][0]);
    const inherited=this.inherit(first.entry,map,{label,site});
    for(const {entry,correspondence} of candidates)correspondence.set(entry.id,inherited.id);
    return inherited;
  }
}
