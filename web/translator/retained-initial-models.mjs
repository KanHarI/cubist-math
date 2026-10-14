// Checked entry for an already resolved initial/free request. Source entry
// supplies one complete header (type = theory application, value = optional
// generator type); this boundary does no additional source name resolution.
import {bindingResolution} from "../cubist/bindings.mjs";
import {bindingSyntaxView} from "../cubist/binding-syntax.mjs";
import {retainedInitialArtifacts} from "../cubist/retained-initial-artifacts.mjs";
import {bindingDeclaration,lowerBindingDeclaration} from "./binding-module.mjs";
import {checkedInitialArguments,equationalSupport} from "./initial-models.mjs";

export function retainedInitialDeclarations(t,module,{record,binding,header,free=false,...site},env,{owner}) {
  const table=t.compilationBindings.table,theory=header.tree.type;
  const head=theory?.kind==="call"?theory.fn:theory;
  if(head?.kind!=="bindingReference"||head.resolution.tag!=="binding"||head.resolution.id!==record.modelId)
    throw new TypeError("An initial request must name its retained theory by identity.");
  const lowered=lowerBindingDeclaration(bindingDeclaration(binding,header),table);
  const parameters=[...record.universeLabels.map(name=>({name})),...record.params];
  const values=checkedInitialArguments(t,module.with({bindingAdapter:lowered.adapter}),{
    theory:lowered.declaration.type,params:lowered.declaration.params,parameters,env,name:record.name});
  const view=tree=>bindingSyntaxView(header,tree);
  const args=header.tree.params.map(p=>({kind:"bindingReference",resolution:bindingResolution(p.name.bindingId),
    spelling:p.name.text,origin:p.name.origin,start:p.name.start,end:p.name.end}));
  const given=new Map([...record.universeIds,...record.params.map(p=>p.id)].map((id,k)=>[id,
    view({kind:"instantiated",value:values[k],args,origin:binding.origin,start:theory.start,end:theory.end,synthetic:true})]));
  const built=retainedInitialArtifacts(record,{binding,header,given,...site,
    ...(free?{generator:view(header.tree.value)}:{})},{table,owner,plan:equationalSupport(record)});
  return {...built,declarations:built.artifacts.map(({binding,syntax,...annotations})=>bindingDeclaration(binding,syntax,annotations))};
}
