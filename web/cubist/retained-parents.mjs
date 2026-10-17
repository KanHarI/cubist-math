// Instantiate parent interfaces before cloning their local telescopes.
// Sharing uses explicit origin and binding correspondences; display labels
// choose the public child interface but never decide syntax equality.
import {bindingSyntaxView,remapBindingSyntax,sameBindingSyntax,bindingUses} from "./binding-syntax.mjs";
import {bindingResolution,reservedResolution,applicationResolution,sourceOrigin,expandedOrigin,failedResolution} from "./bindings.mjs";
import {freshName} from "./scopes.mjs";
import {reservedNames} from "./parser.mjs";
import {InheritedInterfaceConflict} from "./retained-interfaces.mjs";
import {correspondingHeaderParameters} from "./telescopes.mjs";
import {inheritNotations} from "./retained-notation.mjs";

const label=parameter=>parameter.label??parameter.name.label??parameter.name.text;
const original=entry=>entry.binding.original??entry.id;
const located=(error,node)=>Object.assign(error,{offset:node.start,sourceEnd:node.end,origin:node.origin});
const snake=text=>text.replace(/([a-z0-9])([A-Z])/g,"$1_$2").toLowerCase();

export function retainParents(theory,interfaces,{lookup,source,owner,constructors=[]},admit) {
  const {table,header}=interfaces,T=theory.name.text,prepared=[];
  for(const parent of theory.parents) {
    const record=lookup(parent.name.text);
    if(!record)throw located(Error(`${parent.name.text} is not a theory here: ${T} extends theories in scope.`),parent.name);
    if(!record.bindingSyntax)throw new TypeError("A retained parent requires its canonical source interface.");
    const parentLabel=parent.label?.text??snake(record.name);
    if(!parent.label&&reservedNames.has(parentLabel))
      throw located(Error(`${parent.name.text}'s label would be ${parentLabel}, which is reserved: label it, as in other : ${parent.name.text}.`),parent.name);
    if(prepared.some(p=>p.label===parentLabel))
      throw located(Error(`${T} has two parents labelled ${parentLabel}: label one, as in other : ${parent.name.text}.`),parent.label??parent.name);
    const universes=record.bindingSyntax.tree.params.filter(p=>p.bound),parameters=record.bindingSyntax.tree.params.filter(p=>!p.bound);
    const correspondence=new Map();
    const headerPairs=correspondingHeaderParameters(record.bindingSyntax.tree.params,header.tree.params);
    for(const [parameter,own] of headerPairs) {
      if(!own)throw located(Error(parameter.bound
        ?record.generatedUniverse
          ?`${T} extends ${record.name}, whose header binds no universe: bind ${label(parameter)}, its public universe parameter, in ${T}'s header, or name that universe in ${record.name}'s header.`
          :`${T} extends ${record.name}, whose header binds the universe ${label(parameter)}: bind ${label(parameter)} in ${T}'s header too.`
        :`${T} extends ${record.name}, whose header has the parameter ${label(parameter)}: give ${T} the parameter ${label(parameter)} with the same type.`),parent.name);
      correspondence.set(parameter.name.bindingId,own.name.bindingId);
    }
    for(const [parameter,own] of headerPairs)if(!parameter.bound) {
      const expected=remapBindingSyntax(bindingSyntaxView(record.bindingSyntax,parameter.type),table,correspondence);
      if(!sameBindingSyntax(expected,bindingSyntaxView(header,own.type)))
        throw located(Error(`${T} extends ${record.name}, whose header has the parameter ${label(parameter)}: give ${T} the parameter ${label(parameter)} with the same type.`),parent.name);
    }
    const entries=(record.entries??[...record.fields,...record.derived??[]]).toSorted((a,b)=>a.interface.length-b.interface.length);
    const names=new Map(),renotated=new Map();
    for(const rename of parent.renaming) {
      const field=entries.find(field=>field.name===rename.from.text);
      if(!field)throw located(Error(`${record.name} has no field ${rename.from.text}; its fields are ${record.fields.map(f=>f.name).join(", ")}.`),rename.from);
      if(names.has(field.id))throw located(Error(`${rename.from.text} is renamed twice.`),rename.from);
      names.set(field.id,rename.to.text);
      if(rename.notation) {
        const arity=field.visible?.length??field.syntax.tree.params.length;
        if(!["operation","derived"].includes(field.kind)||arity!==(rename.notation.unary?1:2))
          throw located(Error(rename.notation.unary?`-x names an operation's one argument; ${rename.from.text} is not an operation of one.`
            :`A notation names an operation's two arguments; ${rename.from.text} is not an operation of two.`),rename.notation);
        renotated.set(field.id,rename);
      }
    }
    for(const entry of entries)if(entry.of&&names.has(entry.of)&&!names.has(entry.id))
      names.set(entry.id,`${names.get(entry.of)}_is_${entry.evidence==="IsSet"?"set":"prop"}`);
    prepared.push({parent,record,label:parentLabel,universes,parameters,entries,correspondence,names,renotated,
      site:sourceOrigin({...source,start:parent.start,end:parent.end})});
  }
  const groups=new Map();
  for(const parent of prepared)for(const entry of parent.entries) {
    const name=parent.names.get(entry.id)??entry.label;
    if(!groups.has(name))groups.set(name,[]);
    groups.get(name).push({entry,parent,correspondence:parent.correspondence});
  }
  const taken=new Set([...groups.keys(),...theory.fields.map(item=>item.name.text)]),ambiguous=new Map(),final=[];
  for(const [name,candidates] of groups) {
    const carriers=candidates.filter(({entry})=>["sort","evidence"].includes(entry.kind));
    if(carriers.length&&carriers.length!==candidates.length)
      throw located(Error(`${T} gets ${name} from ${candidates.map(c=>c.parent.record.name).join(" and ")}, a carrier in one and not in another: rename one, as in ${candidates.at(-1).parent.record.name}(${name} := …).`),candidates.at(-1).parent.parent.name);
    if(carriers.length||new Set(candidates.map(({entry})=>original(entry))).size===1) {
      final.push({name,candidates});continue;
    }
    const ancestors=new Map();
    for(const candidate of candidates) {
      const id=original(candidate.entry);
      if(!ancestors.has(id))ancestors.set(id,{name:freshName(`${candidate.parent.label}_${name}`,taken),candidates:[]});
      ancestors.get(id).candidates.push(candidate);
    }
    ambiguous.set(name,candidates.map(candidate=>({label:candidate.parent.label,parentField:candidate.entry.label,
      field:ancestors.get(original(candidate.entry)).name})));
    final.push(...ancestors.values());
  }
  // Reserve one identity per shared child member. Reserving is not admitting
  // it: signatures are compared under these maps before any clone is kept.
  const byIdentity=new Map();
  for(const group of final) {
    const first=group.candidates[0],binding=table.allocate([...owner,"parent-members"],{
      role:first.entry.binding.role,label:group.name,original:original(first.entry),
      origin:expandedOrigin(first.entry.binding.origin,{kind:"inheritance",site:first.parent.site})});
    group.binding=binding;byIdentity.set(binding.id,group);
    for(const {entry,correspondence} of group.candidates)correspondence.set(entry.id,binding.id);
  }
  // Actual dependencies determine the merged telescope order. Unrelated
  // parents may list independent shared fields in different orders.
  for(const group of final) {
    group.dependencies=new Set();
    for(const {entry,correspondence} of group.candidates)for(const use of bindingUses(entry.syntax,{conditional:true})) {
      const id=use.kind==="binding"?correspondence.get(use.id):null;
      if(id&&byIdentity.has(id)&&id!==group.binding.id)group.dependencies.add(id);
    }
  }
  const remaining=new Set(final),admitted=new Set();
  while(remaining.size) {
    const group=[...remaining].find(group=>[...group.dependencies].every(id=>admitted.has(id)));
    if(!group)throw located(Error(`${T}'s inherited interfaces have cyclic dependencies after sharing.`),theory.name);
    let entry;
    try {entry=interfaces.inheritShared(group.candidates,{label:group.name,site:group.candidates[0].parent.site});}
    catch(error) {
      if(error instanceof InheritedInterfaceConflict) {
        const first=group.candidates[0],last=group.candidates.at(-1);
        throw located(["sort","evidence"].includes(first.entry.kind)
          ?Error(`${T} gets the carrier ${group.name} from ${group.candidates.map(c=>c.parent.record.name).join(" and ")} with different kinds or indices: rename one, as in ${last.parent.record.name}(${group.name} := …).`)
          :Error(`${T} gets a field named ${group.name} from both ${first.parent.record.name} and ${last.parent.record.name}: rename one, as in ${last.parent.record.name}(${group.name} := …).`),last.parent.site);
      }
      throw located(error,group.candidates.at(-1).parent.site);
    }
    admit(entry);admitted.add(entry.id);remaining.delete(group);
  }
  const headerLabels=new Set(header.tree.params.map(p=>p.name.text));
  // Ambiguity participates in ordered lookup. A later local or an explicit
  // parent selection can shadow it without a separate spelling pre-pass.
  for(const [name,candidates] of ambiguous)if(!headerLabels.has(name))
    interfaces.context=interfaces.context.bind(name,failedResolution(Error(
      `${name} is ambiguous in ${T}: ${candidates.map(e=>`${e.label}'s`).join(" and ")}. Write ${candidates.map(e=>`${e.label}.${e.parentField}`).join(" or ")}, or rename one in extends.`)));
  for(const parent of prepared)if(!headerLabels.has(parent.label)) {
    const argumentsOf=entries=>entries.map(entry=>bindingResolution(parent.correspondence.get(entry)));
    const type=applicationResolution(bindingResolution(parent.record.modelId),argumentsOf(
      [...parent.universes,...parent.parameters].map(p=>p.name.bindingId)));
    const value=applicationResolution(bindingResolution(parent.record.makeId),argumentsOf(
      [...parent.parameters.map(p=>p.name.bindingId),...parent.record.fields.map(field=>field.id)]));
    const receiver=applicationResolution(reservedResolution("typed"),[type,value]);
    interfaces.context=interfaces.context.namespace(parent.label,parent.entries.map(entry=>
      [entry.label,bindingResolution(parent.correspondence.get(entry.id))]),parent.record.name,{receiver});
  }
  const parents=prepared.map(parent=>({label:parent.label,theory:parent.record.name,modelId:parent.record.modelId,makeId:parent.record.makeId,
    ...(parent.record.homId?{homId:parent.record.homId,homMakeId:parent.record.homMakeId}:{}),
    homSupport:parent.record.homSupport??(parent.record.noMorphisms?{status:"unsupported",reason:parent.record.noMorphisms}
      :{status:"pending",obligations:[{kind:"parent-Hom",theory:parent.record.name}]}),
    universeIds:parent.universes.map(p=>parent.correspondence.get(p.name.bindingId)),
    parameterIds:parent.parameters.map(p=>parent.correspondence.get(p.name.bindingId)),
    fieldIds:parent.record.fields.map(field=>parent.correspondence.get(field.id)),
    kinds:parent.record.fields.map(field=>field.kind),
    homFieldIds:[...parent.record.fields,...(parent.record.derived??[]).filter(field=>field.implementedKind==="operation")]
      .map(field=>parent.correspondence.get(field.id)),
    homKinds:[...parent.record.fields,...(parent.record.derived??[]).filter(field=>field.implementedKind==="operation")]
      .map(field=>field.implementation?"operation":field.kind)}));
  return {parents,ambiguous,...inheritNotations(prepared,{table,owner,source,constructors,context:interfaces.context,theory:T})};
}
