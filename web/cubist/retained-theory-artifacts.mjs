// Base theory artifacts are compositions of retained interfaces. Source
// syntax never enters name resolution here: header and field substitutions
// are explicit identities, and every emitted declaration owns fresh locals.
import {bindingSyntaxView} from "./binding-syntax.mjs";
import {HelperExpansion} from "./helper-expansion.mjs";
import {freshName,scopeMapped,unlinked} from "./scopes.mjs";
export {retainedMorphismArtifacts} from "./retained-morphism-artifacts.mjs";

import {ArtifactBuilder,at,reference,token,call} from "./artifact-builder.mjs";

// Return inert artifacts; the translator's bindingDeclaration boundary puts
// them on its ordinary checked/publication queue. Declaration identities are
// reserved together before construction, independently of their availability.
export function retainedTheoryArtifacts(record,{table,owner,bindings=new Map()}) {
  const {bindingSyntax:header,fields,derived=[]}=record;
  if(!header||header.tree.kind!=="def"||!fields.length)
    throw new TypeError("A retained theory needs its header and at least one complete field interface.");
  const origin=record.origin??header.tree.name.origin;
  if(!origin)throw new TypeError("A generated theory needs a source-qualified request origin.");
  const view=tree=>bindingSyntaxView(header,tree);
  const parents=record.parents??[];
  const labels=[record.name,`${record.name}.make`,...[...fields,...derived].map(field=>`${record.name}.${field.label}`),
    ...parents.map(parent=>`${record.name}.${parent.label}`)];
  if(new Set(labels).size!==labels.length)throw new TypeError("Generated declaration labels must be distinct.");
  const builder=new ArtifactBuilder(header,{table,owner,origin,bindings});
  for(const label of labels)builder.reserve(label);
  const entries=[...fields,...derived],helpers=new HelperExpansion(entries,{table,owner:[...owner,"helpers"]});
  const views=new Map(fields.map(field=>[field.id,helpers.type(field)]));
  const fieldTypes=new Map([...views].map(([id,view])=>[id,view.checking]));
  const taken=new Set([...entries.flatMap(entry=>[entry.label,...entry.syntax.tree.params.map(p=>p.name.text)]),
    ...header.tree.params.map(p=>p.name.text)]);
  // Public call labels stay on the parameters; generated binder labels avoid
  // the source members' own labels, including shadowing helper parameters.
  const headerParams=header.tree.params.map(p=>({...p,label:p.label??p.name.label??p.name.text,
    name:{...p.name,text:freshName(p.name.text,taken),label:p.label??p.name.label??p.name.text}}));
  const universes=headerParams.filter(p=>p.bound);
  if(!universes.length)throw new TypeError("A retained theory header must include its generated or explicit universe.");
  const headerParameters=mode=>headerParams.map(p=>({...unlinked(p),
    ...(mode==="all"||mode==="universes"&&p.bound?{implicit:true}:{})}));
  const headerArguments=headerParams.map(p=>reference(table.get(p.name.bindingId)));
  const modelType=()=>call(reference(bindings.get(record.name)),headerArguments,origin);
  const nextGroup=1+Math.max(-1,...headerParams.map(p=>p.group??0));
  const substitute=(syntax,map)=>builder.substitute(syntax,map);
  const artifacts=builder.artifacts;
  const emit=(label,params,type,value,generated,{inferred=false,body=null,computable=false}={})=>{
    const binding=bindings.get(label),site=entries.find(entry=>entry.label===generated.field)?.binding.origin??origin;
    const declaration={kind:"def",name:{...token(binding),...at(site)},params,type,...at(site),
      ...(inferred?{value}:{body:body??[{kind:"exact",value,...at(origin)}],typedValue:true}),
      ...(computable?{computable:true}:{}),
      ...(params.some(p=>p.implicit)?{implicitParameters:at(origin)}:{})};
    builder.emit(binding,declaration,{theory:record.name,
      family:generated.role==="derived"?`derived:${generated.field}`:"base",...generated},{inferred});
  };
  const local=(label,source=origin)=>builder.local(label,source);

  // Model type: a dependent tuple closes each field identity with its own
  // fresh binder, after its complete type has been instantiated.
  const fieldLocals=new Map(fields.map(field=>[field.id,local(field.label,field.binding.origin)]));
  const fieldMap=new Map([...fieldLocals].map(([id,binding])=>[id,view(reference(binding))]));
  let modelBody=substitute(fieldTypes.get(fields.at(-1).id),fieldMap).tree;
  for(let k=fields.length-2;k>=0;k--) {
    const field=fields[k];
    modelBody={kind:"exists",name:token(fieldLocals.get(field.id)),binderKind:"exists",
      domain:substitute(fieldTypes.get(field.id),fieldMap).tree,body:modelBody,...at(field.binding.origin)};
  }
  emit(record.name,headerParameters(),null,modelBody,{role:"model"},{inferred:true});

  // Constructor: the same dependent interface, closed by parameters. Each
  // declaration clone below gives these binders independent identities.
  const fieldParameters=fields.map((field,k)=>({name:token(fieldLocals.get(field.id)),
    type:substitute(fieldTypes.get(field.id),fieldMap).tree,group:nextGroup+k}));
  let tuple=reference(fieldLocals.get(fields.at(-1).id));
  for(let k=fields.length-2;k>=0;k--)tuple={kind:"pair",left:reference(fieldLocals.get(fields[k].id)),right:tuple,...at(origin)};
  emit(`${record.name}.make`,[...headerParameters("universes"),...fieldParameters],modelType(),tuple,{role:"make"});

  const model=local(freshName("m",taken)),modelReference=reference(model);
  const modelParameter={name:token(model),type:modelType(),group:nextGroup};
  const projected=new Map(entries.map(entry=>[entry.id,
    view(call(reference(bindings.get(`${record.name}.${entry.label}`)),[modelReference],origin))]));
  fields.forEach((field,k)=>{
    let value=modelReference;
    for(let j=0;j<k;j++)value={kind:"projection",value,index:2,...at(origin)};
    if(k<fields.length-1)value={kind:"projection",value,index:1,...at(origin)};
    emit(`${record.name}.${field.label}`,[...headerParameters("all"),modelParameter],
      substitute(fieldTypes.get(field.id),projected).tree,value,{role:"projection",field:field.label});
  });
  for(const entry of derived) {
    let syntax=entry.syntax;
    if(entry.recursive) {
      // Structural recursion needs a saturated call of this declaration,
      // with its fixed model argument. Only exact self IDs are rewritten.
      const map=tree=>scopeMapped(tree,{deferred:true,extend:scope=>scope,enter(node) {
        if(node.kind!=="call"||node.fn.kind!=="bindingReference"||node.fn.resolution.tag!=="binding"
          ||node.fn.resolution.id!==entry.id)return node;
        return {...node,fn:{...reference(bindings.get(`${record.name}.${entry.label}`)),origin:node.fn.origin},
          args:[modelReference,...node.args.map(map)]};
      }},null);
      syntax=bindingSyntaxView(syntax,map(syntax.tree),{inferred:syntax.inferred});
    }
    const instantiated=substitute(syntax,projected),tree=instantiated.tree;
    const params=tree.params.map(p=>({...p,group:nextGroup+1+(p.group??0)}));
    emit(`${record.name}.${entry.label}`,[...headerParameters("all"),modelParameter,...params],tree.type,tree.value,
      {role:"derived",field:entry.label},{inferred:syntax.inferred,computable:tree.computable,
        body:tree.body??(tree.value===undefined?null:[{kind:"exact",value:tree.value,...at(tree.value.origin??origin)}])});
  }
  for(const parent of parents) {
    const headerIds=new Set(header.tree.params.map(p=>p.name.bindingId));
    if(!Array.isArray(parent.universeIds)||!Array.isArray(parent.parameterIds)||!Array.isArray(parent.fieldIds)
      ||[...parent.universeIds,...parent.parameterIds].some(id=>!headerIds.has(id))
      ||parent.fieldIds.some(id=>!fieldTypes.has(id)))
      throw new TypeError("A parent projection needs a complete child header and field correspondence.");
    const parentModel=table.get(parent.modelId),parentMake=table.get(parent.makeId);
    if(parentModel.role!=="declaration"||parentMake.role!=="declaration")
      throw new TypeError("A parent projection needs its parent's declaration identities.");
    const args=ids=>ids.map(id=>reference(table.get(id)));
    emit(`${record.name}.${parent.label}`,[...headerParameters("all"),modelParameter],
      call(reference(parentModel),args([...parent.universeIds,...parent.parameterIds]),origin),
      call(reference(parentMake),[...args(parent.parameterIds),...parent.fieldIds.map(id=>projected.get(id).tree)],origin),
      {role:"projection",field:parent.label});
  }
  const retainedRecord={...record,model:record.name,make:`${record.name}.make`,
    modelId:bindings.get(record.name).id,makeId:bindings.get(`${record.name}.make`).id,
    universeLabels:universes.map(p=>p.label),
    universeIds:universes.map(p=>p.name.bindingId),
    params:header.tree.params.filter(p=>!p.bound).map(p=>({id:p.name.bindingId,name:p.label??p.name.text,type:p.type,group:p.group})),
    fields:fields.map(field=>({...field,name:field.label,type:views.get(field.id).analysis.tree,
      projection:`${record.name}.${field.label}`,projectionId:bindings.get(`${record.name}.${field.label}`).id})),
    derived:derived.map(entry=>({...entry,name:entry.label,projection:`${record.name}.${entry.label}`,
      projectionId:bindings.get(`${record.name}.${entry.label}`).id})),
    parents:parents.map(parent=>({...parent,projection:`${record.name}.${parent.label}`,
      projectionId:bindings.get(`${record.name}.${parent.label}`).id}))};
  artifacts[0].theory=retainedRecord;
  return {artifacts,bindings,views,record:retainedRecord};
}
