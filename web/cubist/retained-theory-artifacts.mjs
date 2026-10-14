// Base theory artifacts are compositions of retained interfaces. Source
// syntax never enters name resolution here: header and field substitutions
// are explicit identities, and every emitted declaration owns fresh locals.
import {bindingResolution,reservedResolution,expandedOrigin,LexicalContext} from "./bindings.mjs";
import {bindingSyntaxView,cloneBindingSyntax,substituteBindingSyntax,resolveBindingTemplate,bindingUses} from "./binding-syntax.mjs";
import {HelperExpansion} from "./helper-expansion.mjs";
import {freshName,scopeMapped,rewritten,relocated} from "./scopes.mjs";
import {parse,reservedReferences} from "./parser.mjs";
import {morphismSource} from "./morphisms.mjs";

const at=origin=>({start:origin.start,end:origin.end,origin,synthetic:true});
const reference=binding=>({kind:"bindingReference",resolution:bindingResolution(binding.id),
  spelling:binding.label,...at(binding.origin)});
const builtin=(label,origin)=>({kind:"bindingReference",resolution:reservedResolution(label),spelling:label,...at(origin)});
const token=binding=>({text:binding.label,bindingId:binding.id,bindingRole:binding.role,...at(binding.origin)});
const call=(fn,args,origin)=>({kind:"call",fn,args,...at(origin)});

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
  for(const label of labels) {
    if(bindings.has(label)) {
      const binding=table.get(bindings.get(label).id);
      if(binding.role!=="declaration"||binding.label!==label)
        throw new TypeError("A generated declaration has an incompatible reserved identity.");
    } else bindings.set(label,table.allocate([...owner,"declarations"],{role:"declaration",label,origin}));
  }
  const entries=[...fields,...derived],helpers=new HelperExpansion(entries,{table,owner:[...owner,"helpers"]});
  const views=new Map(fields.map(field=>[field.id,helpers.type(field)]));
  const fieldTypes=new Map([...views].map(([id,view])=>[id,view.checking]));
  const taken=new Set([...entries.flatMap(entry=>[entry.label,...entry.syntax.tree.params.map(p=>p.name.text)]),
    ...header.tree.params.map(p=>p.name.text)]);
  // Public call labels stay on the parameters; generated binder labels avoid
  // the source members' own labels, including shadowing helper parameters.
  const headerParams=header.tree.params.map(p=>({...p,label:p.label??p.name.label??p.name.text,
    name:{...p.name,text:freshName(p.name.text,taken),label:undefined}}));
  const universes=headerParams.filter(p=>p.bound);
  if(!universes.length)throw new TypeError("A retained theory header must include its generated or explicit universe.");
  const headerParameters=mode=>headerParams.map(p=>({...p,
    ...(mode==="all"||mode==="universes"&&p.bound?{implicit:true}:{})}));
  const headerArguments=headerParams.map(p=>reference(table.get(p.name.bindingId)));
  const modelType=()=>call(reference(bindings.get(record.name)),headerArguments,origin);
  const nextGroup=1+Math.max(-1,...headerParams.map(p=>p.group??0));
  let serial=0;
  const substitute=(syntax,map)=>substituteBindingSyntax(syntax,map,table,[...owner,"substitution",String(serial++)]);
  const artifacts=[];
  const emit=(label,params,type,value,generated,{inferred=false,body=null,computable=false}={})=>{
    const binding=bindings.get(label),declaration={kind:"def",name:token(binding),params,type,...at(origin),
      ...(inferred?{value}:{body:body??[{kind:"exact",value,...at(origin)}],typedValue:true}),
      ...(computable?{computable:true}:{}),
      ...(params.some(p=>p.implicit)?{implicitParameters:at(origin)}:{})};
    const syntax=bindingSyntaxView(header,declaration,{inferred});
    const cloned=cloneBindingSyntax(syntax,table,[...owner,"artifact",String(artifacts.length)],
      {expansion:{kind:"generation",site:origin}}).syntax;
    artifacts.push({binding,syntax:cloned,generated:{theory:record.name,
      family:generated.role==="derived"?`derived:${generated.field}`:"base",...generated}});
  };
  const local=(label,source=origin)=>table.allocate([...owner,"locals"],
    {role:"parameter",label,origin:expandedOrigin(source,{kind:"generation",site:origin})});
  const max=values=>values.length===1?values[0]:call(builtin("max",origin),[values[0],max(values.slice(1))],origin);
  const modelUniverse=call(builtin("next",origin),[max(universes.map(p=>reference(table.get(p.name.bindingId))))],origin);

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
  emit(record.name,headerParameters(),modelUniverse,modelBody,{role:"model"});

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
        body:tree.body??(tree.value===undefined?null:[{kind:"exact",value:tree.value,...at(origin)}])});
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
    universes:universes.map(p=>p.label),universeLabels:universes.map(p=>p.label),
    universeIds:universes.map(p=>p.name.bindingId),
    params:header.tree.params.filter(p=>!p.bound).map(p=>({id:p.name.bindingId,name:p.label??p.name.text,type:p.type,group:p.group})),
    fields:fields.map(field=>({...field,name:field.label,type:views.get(field.id).analysis.tree,
      checkingType:views.get(field.id).checking,obligations:views.get(field.id).obligations,
      projection:`${record.name}.${field.label}`,projectionId:bindings.get(`${record.name}.${field.label}`).id})),
    derived:derived.map(entry=>({...entry,name:entry.label,projection:`${record.name}.${entry.label}`,
      projectionId:bindings.get(`${record.name}.${entry.label}`).id})),
    notations:record.notations??{},parents:parents.map(parent=>({...parent,projection:`${record.name}.${parent.label}`,
      projectionId:bindings.get(`${record.name}.${parent.label}`).id}))};
  artifacts[0].theory=retainedRecord;
  return {artifacts,bindings,views,record:retainedRecord};
}

// Until CB4 replaces the Hom/Iso templates, only the template-owned text is
// parsed. Each source fragment is spliced under an explicit correspondence
// to the already-resolved template binders and generated declarations.
export function retainedMorphismArtifacts(record,{table,owner,bindings,outerReferences=null,isTheory}) {
  const plan=morphismSource(record,isTheory),artifacts=[];
  const support={homSupport:plan.support,isoSupport:plan.isoSupport,
    ...(plan.missing?{noMorphisms:plan.missing}:{}),...(plan.missingIso?{noIsomorphisms:plan.missingIso}:{})};
  if(!plan.declarations)return {plan,artifacts,bindings,record:{...record,...support}};
  const origin=record.origin??record.bindingSyntax.tree.name.origin;
  const view=tree=>bindingSyntaxView(record.bindingSyntax,tree);
  for(const declaration of plan.declarations) {
    if(bindings.has(declaration.name))throw new TypeError("A morphism artifact identity is already reserved.");
    bindings.set(declaration.name,table.allocate([...owner,"declarations"],{role:"declaration",label:declaration.name,origin}));
  }
  if(!outerReferences) {
    outerReferences=new Map();
    for(const parent of record.parents)for(const [name,id] of [[`${parent.theory}.Hom`,parent.homId],[`${parent.theory}.Hom.make`,parent.homMakeId]])if(id) {
      if(outerReferences.has(name)&&outerReferences.get(name).id!==id)
        throw new TypeError("Parent template references require distinct declaration markers.");
      outerReferences.set(name,table.get(id));
    }
  }
  let serial=0;
  const local=(context,label)=>{
    const resolution=context.lookup(label);
    if(resolution.tag!=="binding")throw new TypeError(`A template interface has no local binding for ${label}.`);
    return view({...reference(table.get(resolution.id)),spelling:label});
  };
  const instantiate=(tree,context,{universes,model,locals=new Map()})=>{
    const syntax=view(tree),needed=new Set(bindingUses(syntax,{conditional:true}).filter(use=>use.kind==="binding").map(use=>use.id));
    const replacements=new Map();
    record.universeIds.forEach((id,k)=>{if(needed.has(id))replacements.set(id,local(context,universes[k]));});
    for(const parameter of record.params)if(needed.has(parameter.id))replacements.set(parameter.id,local(context,parameter.name));
    for(const [id,label] of locals)if(needed.has(id))replacements.set(id,local(context,label));
    for(const field of record.fields)if(needed.has(field.id)) {
      if(!model)throw new TypeError("A retained field needs an explicit template model.");
      replacements.set(field.id,view(call(reference(table.get(field.projectionId)),[local(context,model).tree],origin)));
    }
    return substituteBindingSyntax(syntax,replacements,table,[...owner,"splice",String(serial++)]);
  };
  const splices=new Map([
    ...record.params.map((parameter,k)=>[plan.parameterMarker(k),context=>instantiate(parameter.type,context,{universes:plan.universes})]),
    ...[...plan.typeMarkers].map(([marker,payload])=>[marker,context=>instantiate(payload.type,context,payload)]),
    ...[...plan.references].map(([marker,{name,scope}])=>[marker,()=>{
      const binding=(scope==="generated"?bindings:scope==="outer"?outerReferences:null)?.get(name);
      if(!binding)throw new TypeError(`A template declaration needs an explicit ${scope} identity for ${name}.`);
      return view(reference(table.get(binding.id)));
    }]),
  ]);
  for(const [index,declaration] of plan.declarations.entries()) {
    const source=declaration.source.replace(/^def \S+?(?=[{(:])/,`def generated_${index}`);
    let tree=relocated(parse(source).declarations[0],at(origin));
    tree=rewritten(tree,node=>node.kind==="name"&&splices.has(node.name)
      ?{kind:"templateHole",hole:node.name,...at(origin)}:node);
    for(const parameter of tree.params??[])if(Object.hasOwn(declaration.labels??{},parameter.name.text))
      parameter.label=declaration.labels[parameter.name.text];
    const context=new LexicalContext(reservedReferences(source).map(label=>[label,reservedResolution(label)]));
    const syntax=resolveBindingTemplate(tree,{table,owner:[...owner,"artifact",String(index)],context,source:origin},splices);
    const theory=declaration.record?{...declaration.record,modelId:bindings.get(declaration.record.model).id,
      makeId:bindings.get(declaration.record.make).id,
      fields:declaration.record.fields.map(field=>({...field,projectionId:bindings.get(field.projection).id})),
      parents:declaration.record.parents.map(parent=>({...parent,projectionId:bindings.get(parent.projection).id}))}:null;
    artifacts.push({binding:bindings.get(declaration.name),syntax,
      generated:{theory:record.name,role:declaration.role,family:declaration.family,...(declaration.field?{field:declaration.field}:{})},
      ...(theory?{theory}:{})});
  }
  return {plan,artifacts,bindings,record:{...record,...support,
    homId:bindings.get(`${record.name}.Hom`).id,homMakeId:bindings.get(`${record.name}.Hom.make`).id}};
}
