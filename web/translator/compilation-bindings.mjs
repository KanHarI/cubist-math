// Identities belong to the compilation, independently of optional inspection
// and scope collection. This registry records declarations, not availability:
// only the checked environment/publication groups supply elaboration values.
import {BindingTable,sourceOrigin} from "../cubist/bindings.mjs";

export const declarationIdentity=value=>value?.tag==="DefRef"?value.name
  :value?.tag==="InductiveConstructor"?`${value.inductive.binding}:constructor:${value.index}`:value?.binding;

export class CompilationBindings {
  #declarations=new Map();
  #owners=new Map();
  constructor(revision,{table=new BindingTable(revision)}={}) {
    if(table.revision!==revision)throw new TypeError("Compilation binding revision mismatch.");
    this.revision=revision;this.table=table;
  }
  declaration(key) {return this.#declarations.get(key)??null;}
  declare(module,declaration,key) {
    // A rejected duplicate does not reassign the original declaration's
    // identity or source owner. Reservation itself grants no checked value.
    if(this.#declarations.has(key))return this.#declarations.get(key).binding;
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
    for(const [index,constructor] of (declaration.constructors??[]).entries()) {
      const identity=`${key}:constructor:${index}`;
      register(identity,constructor.name,["constructor",String(index)]);
      // A refused constructor can still be described by its declared key.
      const name=`${module}__${constructor.name.text}`;
      if(!this.#declarations.has(name))this.#declarations.set(name,this.#declarations.get(identity));
    }
    return binding;
  }
  ofValue(value,{moduleName}={}) {
    const key=declarationIdentity(value)??(value?.tag==="Recursive"&&moduleName?`${moduleName}__${value.source}`:null);
    return key?this.declaration(key)?.binding??null:null;
  }
}
