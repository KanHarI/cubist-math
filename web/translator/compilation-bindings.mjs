// Identities belong to the compilation, independently of optional inspection
// and scope collection. This registry records declarations, not availability:
// only the checked environment/publication groups supply elaboration values.
import {BindingTable,sourceOrigin} from "../cubist/bindings.mjs";
import {alphaKey,isTerm,freeNames} from "./core.mjs";
import {freeDimensions} from "./dimension-slots.mjs";

export const declarationIdentity=value=>value?.tag==="DefRef"?value.name
  :value?.tag==="InductiveConstructor"?`${value.inductive.binding}:constructor:${value.index}`:value?.binding;

export class CompilationBindings {
  #declarations=new Map();
  #owners=new Map();
  #captures=new Map();
  #modelNotations=new Map();
  #published=new WeakMap();
  // The module that first declared each key, module__name. Two modules'
  // spellings can join to one key, as a::b__c and a__b::c do: the key stays
  // the first module's, and its checker refuses the other's declaration.
  #keyModules=new Map();
  constructor(revision,{table=new BindingTable(revision)}={}) {
    if(table.revision!==revision)throw new TypeError("Compilation binding revision mismatch.");
    this.revision=revision;this.table=table;
  }
  declaration(key) {return this.#declarations.get(key)??null;}
  declarationEntries() {return this.#declarations.entries();}
  // The module that declared `key`, or undefined.
  keyModule(key) {return this.#keyModules.get(key);}
  declare(module,declaration,key) {
    // A rejected duplicate does not reassign the original declaration's
    // identity or source owner. Reservation itself grants no checked value.
    if(this.#declarations.has(key))return this.#declarations.get(key).binding;
    this.#keyModules.set(key,module);
    const index=this.#owners.get(module)??0;
    this.#owners.set(module,index+1);
    const owner=["declarations",module,String(index)];
    const register=(identity,token,suffix=[])=>{
      if(this.#declarations.has(identity))return this.#declarations.get(identity).binding;
      const binding=token.bindingId?this.table.get(token.bindingId):this.table.allocate([...owner,...suffix],{
        role:"declaration",label:token.label??token.text,
        origin:token.origin??sourceOrigin({revision:this.revision,module,start:token.start,end:token.end}),
      });
      this.#declarations.set(identity,Object.freeze({binding,generated:!!declaration.generated||declaration.kind==="theory"}));
      return binding;
    };
    const binding=register(key,declaration.name);
    const constructors=[...(declaration.constructors??[])];
    if(declaration.kind==="inductive"&&declaration.result?.modifier&&declaration.result.modifier.kind!=="type")
      constructors.push({name:{text:`${declaration.name.text}.squash`,label:`${declaration.name.label??declaration.name.text}.squash`,
        start:declaration.name.start,end:declaration.name.end,origin:declaration.name.origin}});
    for(const [index,constructor] of constructors.entries()) {
      const identity=`${key}:constructor:${index}`;
      register(identity,constructor.name,["constructor",String(index)]);
      // A refused constructor can still be described by its declared key.
      const name=`${module}__${constructor.name.text}`;
      if(!this.#declarations.has(name)) {
        this.#declarations.set(name,this.#declarations.get(identity));
        this.#keyModules.set(name,module);
      }
    }
    return binding;
  }
  ofValue(value,{moduleName}={}) {
    const published=value&&typeof value==="object"?this.#published.get(value):null;
    if(published)return published;
    const key=declarationIdentity(value)??(value?.tag==="Recursive"&&moduleName?`${moduleName}__${value.source}`:null);
    return key?this.declaration(key)?.binding??null:null;
  }
  // Publication knows the exact declaration even when its checked reference
  // applies implicit logical assumptions. This receipt is not structural term
  // equality and grants no availability outside the current environment.
  published(binding,value) {
    this.table.get(binding.id);
    const previous=this.#published.get(value);
    if(previous&&previous.id!==binding.id)throw new TypeError("A published value has conflicting declaration identities.");
    this.#published.set(value,binding);
  }
  // A checked closed receiver has one semantic identity in this compilation.
  // Source activations remain separate occurrences with their own origins.
  // This registry grants no availability: the consumer still carries the
  // captured value explicitly in its environment, after checking activation.
  capture(value,origin) {
    if(!isTerm(value)||freeNames(value).size||freeDimensions(value).size)
      throw new TypeError("A source capture requires a closed core value.");
    const declared=this.ofValue(value);
    if(declared)return declared;
    const key=alphaKey(value);
    if(!this.#captures.has(key))this.#captures.set(key,this.table.allocate(["captures"],{
      role:"capture",label:"selection receiver",origin,
    }));
    return this.#captures.get(key);
  }
  // A model's complete notation has the receiver's semantic identity, but
  // lives in a separate namespace from terms. Source activation occurrences
  // keep their own histories. An attached extension contributes its rule
  // identity: the same model with different readers is a different context.
  captureModelNotation(receiver,origin,extension=null) {
    this.table.get(receiver.id);
    if(extension&&this.table.get(extension).role!=="notation")throw new TypeError("A model extension needs a notation identity.");
    const key=JSON.stringify([receiver.id,extension]);
    if(!this.#modelNotations.has(key))this.#modelNotations.set(key,
      this.table.allocate(["model-notation-captures"],{role:"capture",label:"selected notation",origin}));
    return this.#modelNotations.get(key);
  }
}
