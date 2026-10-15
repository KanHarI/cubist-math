// Checked entry for an already resolved initial/free request. Source entry
// supplies one complete header (type = theory application, value = optional
// generator type); this boundary does no additional source name resolution.
import {bindingResolution} from "../cubist/bindings.mjs";
import {bindingSyntaxView} from "../cubist/binding-syntax.mjs";
import {retainedInitialArtifacts} from "../cubist/retained-initial-artifacts.mjs";
import {bindingDeclaration,lowerBindingDeclaration} from "./binding-module.mjs";
import {checkedInitialArguments,equationalSupport,notATheory,recursiveGenerators} from "./initial-models.mjs";
import {sourceBindingInputs} from "./binding-module.mjs";
import {activateSourceItem,withSourceCaptures} from "./retained-source-context.mjs";
import {resolveBindingSyntax,bindingUses} from "../cubist/binding-syntax.mjs";
import {reservedReferences} from "../cubist/parser.mjs";
import {sourceOrigin} from "../cubist/bindings.mjs";
import {repeatedName} from "./names.mjs";
import {Scope} from "./elaboration.mjs";

export function retainedInitialSource(t,module,declaration,env) {
  const registry=t.compilationBindings,table=registry.table;
  const owner=["initial-source",module.moduleName,String(declaration.start)];
  const source={revision:registry.revision,module:module.moduleName};
  const inputs=sourceBindingInputs(registry,env,{reserved:reservedReferences(module.source)});
  const prepared=activateSourceItem(t,new Scope(module,new Map(),new Map([...env,...inputs.env])),
    declaration,inputs,{owner,source});
  const captures=withSourceCaptures(new Map([...env,...inputs.env]),prepared,inputs.adapter);
  // The request's theory head belongs to the enclosing source scope; only
  // its arguments and generator live under the request's parameter telescope.
  const head=declaration.theory.kind==="call"?declaration.theory.fn:declaration.theory;
  const headSyntax=resolveBindingSyntax(head,{table,owner:[...owner,"theory"],source,
    context:prepared.context,constructors:inputs.constructors});
  const resolution=headSyntax.tree.resolution;
  const value=resolution?.tag==="binding"?captures.get(inputs.adapter.key(resolution.id)):null;
  if(value?.tag==="Untranslated")throw module.locate(Object.assign(Error(`Untranslated dependency: ${head.name}`),
    {blockedBy:value.blockedBy??value.binding,cause:value.cause??value.reason}),head);
  const record=value?.tag==="DefRef"?t.checker.theories?.get(value.name):null;
  if(!record?.bindingSyntax)throw module.locate(notATheory(declaration.kind,
    module.source.slice(declaration.theory.start,declaration.theory.end).trim()),declaration.theory);
  const repeated=repeatedName(declaration.params);
  if(repeated)throw module.locate(Error(`${declaration.name.text} has two parameters named ${repeated.name.text}: give each its own name.`),repeated.name);
  const binding=table.allocate([...owner,"declaration"],{role:"declaration",label:declaration.name.text,
    origin:sourceOrigin({...source,start:declaration.name.start,end:declaration.name.end})});
  const header=resolveBindingSyntax({kind:"def",name:declaration.name,params:declaration.params,
    type:declaration.theory,value:declaration.on??null},
  {table,owner:[...owner,"header"],source,context:prepared.context,constructors:inputs.constructors,
    fixedReferences:new Map([[head,resolution]])});
  if(declaration.kind==="free"&&bindingUses(bindingSyntaxView(header,header.tree.value)).some(use=>
    use.kind==="missing"&&(use.label===declaration.name.text||use.label.startsWith(`${declaration.name.text}.`))))
    throw module.locate(recursiveGenerators(declaration.name.text),declaration.on);
  const built=retainedInitialDeclarations(t,module,{record,binding,header,free:declaration.kind==="free",
    theorySpan:declaration.theory,generatorSpan:declaration.on},captures,{owner});
  if(built.plan.status!=="conditional")throw module.locate(Error(built.plan.reason
    ??"The equational strategy needs resolved field interfaces."),declaration.theory);
  for(const [key,value] of captures)env.set(key,value);
  return built.declarations;
}

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
