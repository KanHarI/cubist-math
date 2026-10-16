// Shared construction for generated retained syntax. This boundary allocates
// identities and freshens artifacts; it never resolves source spellings.
import {bindingResolution,reservedResolution,expandedOrigin} from "./bindings.mjs";
import {bindingSyntaxView,cloneBindingSyntax,substituteBindingSyntax} from "./binding-syntax.mjs";

export const at=origin=>({start:origin.start,end:origin.end,origin,synthetic:true});
export const reference=binding=>({kind:"bindingReference",resolution:bindingResolution(binding.id),
  spelling:binding.label,...at(binding.origin)});
export const builtin=(label,origin)=>({kind:"bindingReference",resolution:reservedResolution(label),spelling:label,...at(origin)});
export const token=binding=>({text:binding.label,bindingId:binding.id,bindingRole:binding.role,...at(binding.origin)});
export const call=(fn,args,origin)=>({kind:"call",fn,args,...at(origin)});

export class ArtifactBuilder {
  constructor(header,{table,owner,origin,bindings=new Map()}) {
    Object.assign(this,{header,table,owner,origin,bindings,artifacts:[],serial:0});
  }
  reserve(label) {
    if(this.bindings.has(label)) {
      const binding=this.table.get(this.bindings.get(label).id);
      if(binding.role!=="declaration"||binding.label!==label)
        throw new TypeError("A generated declaration has an incompatible reserved identity.");
    } else this.bindings.set(label,this.table.allocate([...this.owner,"declarations"],
      {role:"declaration",label,origin:this.origin}));
    return this.bindings.get(label);
  }
  local(label,origin=this.origin,role="parameter") {
    return this.table.allocate([...this.owner,"locals"],
      {role,label,origin:expandedOrigin(origin,{kind:"generation",site:this.origin})});
  }
  substitute(syntax,replacements) {
    return substituteBindingSyntax(syntax,replacements,this.table,[...this.owner,"substitution",String(this.serial++)]);
  }
  emit(binding,tree,generated,{inferred=false}={}) {
    const syntax=cloneBindingSyntax(bindingSyntaxView(this.header,tree,{inferred}),this.table,
      [...this.owner,"artifact",String(this.artifacts.length)],{expansion:{kind:"generation",site:this.origin}}).syntax;
    this.artifacts.push({binding,syntax,generated});
  }
}
