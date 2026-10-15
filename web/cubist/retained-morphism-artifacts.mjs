// Hom/Iso declarations compose retained expressions and exact identities.
// Mapping support is independent of construction and checked publication.
import {ArtifactBuilder,at,reference,builtin,token} from "./artifact-builder.mjs";
import {bindingSyntaxView,bindingUses} from "./binding-syntax.mjs";
import {freshName,allNames} from "./scopes.mjs";
import {reservedNames} from "./parser.mjs";
import {morphismPlan} from "./morphisms.mjs";

export function retainedMorphismArtifacts(record,{table,owner,bindings,isTheory=()=>false}) {
  const plan=morphismPlan(record);
  const support={homSupport:plan.support,isoSupport:plan.isoSupport,
    ...(plan.missing?{noMorphisms:plan.missing}:{}),...(plan.missingIso?{noIsomorphisms:plan.missingIso}:{})};
  if(plan.support.status!=="conditional")return {plan,artifacts:[],bindings,record:{...record,...support}};
  const origin=record.origin??record.bindingSyntax.tree.name.origin,site=at(origin);
  const builder=new ArtifactBuilder(record.bindingSyntax,{table,owner,origin,bindings});
  const {artifacts}=builder,{homFields,carrierFields,families,tripped}=plan;
  const hom=`${record.name}.Hom`,iso=`${record.name}.Iso`,single=carrierFields.length===1;
  const isoFields=[{name:"to"},{name:"from"},
    ...tripped.map(field=>({name:single?"from_to":`from_to_${field.name}`,sort:field.id,way:"from_to"})),
    ...tripped.map(field=>({name:single?"to_from":`to_from_${field.name}`,sort:field.id,way:"to_from"}))];
  const familyNames=(name,fields,parents=[])=>[name,`${name}.make`,...fields.map(f=>`${name}.${f.name}`),
    `${name}.id`,`${name}.compose`,...parents.map(p=>`${name}.${p.label}`)];
  for(const name of [...familyNames(hom,homFields,record.parents),
    ...(plan.isoSupport.status==="conditional"?[...familyNames(iso,isoFields),`${iso}.inverse`]:[])]) {
    if(bindings.has(name))throw new TypeError("A morphism artifact identity is already reserved.");
    builder.reserve(name);
  }
  const taken=new Set([...reservedNames,...record.params.map(p=>p.name),
    ...record.fields.flatMap(field=>[...allNames(field.type)]),
    ...[...plan.operations.values()].flatMap(op=>op.inputs.map(p=>p.name)),
    ...[...families.values()].flatMap(indices=>indices.map(p=>p.name))]);
  const avoided={has:name=>name===record.name||isTheory(name)||taken.has(name),add:name=>taken.add(name)};
  const local=(stem,role="local")=>builder.local(freshName(stem,avoided),origin,role);
  const A=local("A","parameter"),B=local("B","parameter"),C=local("C","parameter");
  const f=local("f","parameter"),g=local("g","parameter");
  const count=record.universeIds.length;
  const universes=stem=>Array.from({length:count},(_,k)=>local(count===1?stem:`${stem}_${k+1}`,"universe"));
  const uA=universes("U"),uB=plan.sharedUniverses?uA:universes("V"),uC=plan.sharedUniverses?uA:universes("W");
  const universesAt=model=>model===A?uA:model===B?uB:uC;
  const parameters=new Map(record.params.map(p=>[p.id,local(p.name==="_"?"argument":p.name,"parameter")]));
  const view=tree=>bindingSyntaxView(record.bindingSyntax,tree);
  const ref=id=>reference(table.get(id)),decl=name=>reference(bindings.get(name));
  const apply=(fn,args=[],implicitArgs=null)=>args.length||implicitArgs
    ?{kind:"call",fn,args,...(implicitArgs?{implicitArgs}:{}),...site}:fn;
  const built=(name,args)=>apply(builtin(name,origin),args);
  const binary=(operator,left,right)=>({kind:"binary",operator,left,right,...site});
  const projection=(value,index)=>({kind:"projection",value,index,...site});
  const quantify=(kind,params,body)=>params.reduceRight((body,p)=>({kind,binderKind:kind,
    name:p.name,domain:p.type,body,...site}),body);
  const tuple=values=>values.length===1?values[0]:{kind:"pair",left:values[0],right:tuple(values.slice(1)),...site};
  const fieldById=new Map(record.fields.map(field=>[field.id,field]));
  const projected=(id,model)=>apply(ref(fieldById.get(id).projectionId),[reference(model)]);
  const typeIn=(tree,model,locals=new Map())=>{
    const syntax=view(tree),needed=new Set(bindingUses(syntax,{conditional:true}).filter(use=>use.kind==="binding").map(use=>use.id));
    const map=new Map();
    const put=(id,value)=>{if(needed.has(id))map.set(id,view(value));};
    record.universeIds.forEach((id,k)=>put(id,reference(universesAt(model)[k])));
    for(const [id,binding] of parameters)put(id,reference(binding));
    for(const [id,value] of locals)put(id,value);
    for(const field of record.fields)if(needed.has(field.id))put(field.id,projected(field.id,model));
    return builder.substitute(syntax,map).tree;
  };
  // Each occurrence of a source telescope gets new local IDs. The same
  // family can occur in several disjoint round-trip fields of one artifact.
  const bind=(inputs,typeOf,body,kind="forall")=>{
    const locals=new Map(),params=[];
    for(const input of inputs) {
      const type=typeOf(input,locals),binding=builder.local(input.name,table.get(input.id).origin,"local");
      params.push({name:token(binding),type});locals.set(input.id,reference(binding));
    }
    return quantify(kind,params,body(locals));
  };
  const side=(model,maps=[])=>({model,maps});
  const along=(from,to,mapOf)=>({from,to:side(to.model??to,[...from.maps,mapOf]),mapOf});
  const indexAt=(sort,k,arg,at,locals)=>{
    const index=families.get(sort)[k],value=typeIn(arg,at.model,locals);
    return index.shape.kind==="carrier"?at.maps.reduce((value,mapOf)=>apply(mapOf(index.shape.sort),[value]),value):value;
  };
  const typeAt=(shape,at,locals)=>{
    if(shape.kind==="fixed")return typeIn(shape.type,at.model,locals);
    if(shape.kind==="carrier")return apply(projected(shape.sort,at.model),
      (shape.args??[]).map((arg,k)=>indexAt(shape.sort,k,arg,at,locals)));
    if(shape.kind==="arrow")return binary("->",typeAt(shape.from,at,locals),typeAt(shape.to,at,locals));
    return binary("and",typeAt(shape.left,at,locals),typeAt(shape.right,at,locals));
  };
  const lambda=(binding,type,body)=>quantify("lambda",[{name:token(binding),type}],body);
  const push=(shape,term,step,locals)=>{
    if(shape.kind==="fixed")return term;
    if(shape.kind==="carrier")return apply(step.mapOf(shape.sort),
      [...(shape.args??[]).map((arg,k)=>indexAt(shape.sort,k,arg,step.from,locals)),term]);
    if(shape.kind==="pair")return built("typed",[typeAt(shape,step.to,locals),tuple([
      push(shape.left,projection(term,1),step,locals),push(shape.right,projection(term,2),step,locals)])]);
    const v=local("v");
    return lambda(v,typeAt(shape.from,step.to,locals),
      push(shape.to,apply(term,[pull(shape.from,reference(v),step,locals)]),step,locals));
  };
  const pull=(shape,term,step,locals)=>{
    if(shape.kind==="fixed")return term;
    if(shape.kind==="pair")return built("typed",[typeAt(shape,step.from,locals),tuple([
      pull(shape.left,projection(term,1),step,locals),pull(shape.right,projection(term,2),step,locals)])]);
    const v=local("v");
    return lambda(v,typeAt(shape.from,step.from,locals),
      pull(shape.to,apply(term,[push(shape.from,reference(v),step,locals)]),step,locals));
  };
  const inputType=(input,step,locals)=>typeAt(input.shape,input.way==="pull"?step.to:step.from,locals);
  const preservation=(operation,step)=>bind(operation.inputs,(input,locals)=>inputType(input,step,locals),locals=>{
    const left=apply(projected(operation.id,step.from.model),operation.inputs.map(input=>input.way==="pull"
      ?pull(input.shape,locals.get(input.id),step,locals):locals.get(input.id)));
    const right=apply(projected(operation.id,step.to.model),operation.inputs.map(input=>input.way==="push"
      ?push(input.shape,locals.get(input.id),step,locals):locals.get(input.id)));
    return binary("=",push(operation.result.shape,left,step,locals),right);
  });
  const member=sort=>({kind:"carrier",sort,...(families.has(sort)?{args:families.get(sort).map(index=>ref(index.id))}:{})});
  const familyMap=(sort,step)=>bind(families.get(sort),(index,locals)=>typeAt(index.shape,step.from,locals),locals=>
    binary("->",typeAt(member(sort),step.from,locals),typeAt(member(sort),step.to,locals)));
  const fieldType=(field,mapOf)=>{
    const step=along(side(A),side(B),mapOf);
    return field.sort?(families.has(field.sort)?familyMap(field.sort,step)
      :binary("->",projected(field.sort,A),projected(field.sort,B))):preservation(field.operation,step);
  };
  const memberBody=(sort,at,body,kind="lambda")=>bind(families.get(sort)??[],
    (index,locals)=>typeAt(index.shape,at,locals),locals=>{
      const x=local("x");
      return quantify(kind,[{name:token(x),type:typeAt(member(sort),at,locals)}],body(reference(x),locals));
    },kind);
  const mapped=(fn,sort,at,x,locals)=>apply(fn,
    [...(families.get(sort)??[]).map((index,k)=>indexAt(sort,k,ref(index.id),at,locals)),x]);
  const modelType=model=>apply(ref(record.modelId),[...universesAt(model).map(reference),...[...parameters.values()].map(reference)]);
  const header=(models,withModels=false)=>{
    const levels=[...new Set(models.flatMap(universesAt))];
    const params=[...levels.map(binding=>({name:token(binding),bound:builtin("UU0",origin),group:0,implicit:true})),
      ...record.params.map((p,k)=>({name:{...token(parameters.get(p.id)),label:p.name},label:p.name,
        type:typeIn(p.type,A),group:k+1,implicit:true}))];
    if(withModels)for(const model of models)params.push({name:token(model),type:modelType(model),group:params.length,implicit:true});
    return params;
  };
  const explicit=(params,items)=>[...params,...items.map(([binding,type,label],k)=>({name:{...token(binding),...(label?{label}:{})},
    ...(label?{label}:{}),type,group:params.length+k}))];
  const modelParams=()=>explicit(header([A,B]),[[A,modelType(A)],[B,modelType(B)]]);
  const implicitArgs=(models,withModels=true)=>[...(plan.sharedUniverses?uA:models.flatMap(universesAt)).map(reference),
    ...[...parameters.values()].map(reference),...(withModels?models.map(reference):[])];
  const homType=(from,to)=>apply(decl(hom),[reference(from),reference(to)],implicitArgs([from,to],false));
  const isoType=(from,to)=>apply(decl(iso),[reference(from),reference(to)],implicitArgs([from,to],false));
  const sided=(value,from,to)=>({value,from,to});
  const project=(name,field,h)=>apply(decl(`${name}.${field}`),[h.value],implicitArgs([h.from,h.to]));
  const maps=new Map(homFields.filter(field=>field.sort).map(field=>[field.sort,field]));
  const mapping=(h,sort)=>project(hom,maps.get(sort).name,h);
  const there=i=>sided(project(iso,"to",i),i.from,i.to),back=i=>sided(project(iso,"from",i),i.to,i.from);
  const homLocals=new Map(homFields.map(field=>[field,local(field.name,"parameter")]));
  const isoLocals=new Map(isoFields.map(field=>[field,local(field.name,"parameter")]));
  const bound=field=>(homLocals.has(field)?homLocals:isoLocals).get(field);
  const sigma=(fields,typeOf)=>fields.reduceRight((body,field,k)=>k===fields.length-1?typeOf(field):
    {kind:"exists",binderKind:"exists",name:token(bound(field)),domain:typeOf(field),body,...site},null);
  const declare=(name,params,type,value,role,{field=null,fields=null,parents=[]}={})=>{
    const inferred=type===null;
    builder.emit(bindings.get(name),{kind:"def",name:token(bindings.get(name)),params,type,...site,
      ...(inferred?{value}:{body:[{kind:"exact",value,...site}],typedValue:true}),
      ...(params.some(p=>p.implicit)?{implicitParameters:site}:{})},
      {theory:record.name,family:name===iso||name.startsWith(iso+".")?"iso":"hom",role,...(field?{field}:{})},{inferred});
    if(fields)artifacts.at(-1).theory={name,model:name,make:`${name}.make`,modelId:bindings.get(name).id,makeId:bindings.get(`${name}.make`).id,
      fields:fields.map(field=>({name:field.name,kind:"morphism",projection:`${name}.${field.name}`,projectionId:bindings.get(`${name}.${field.name}`).id})),
      parents:parents.map(parent=>({label:parent.label,projection:`${name}.${parent.label}`,projectionId:bindings.get(`${name}.${parent.label}`).id}))};
  };
  const projections=(name,fields,typeOf)=>fields.forEach((field,k)=>{
    let value=reference(f);
    for(let j=0;j<k;j++)value=projection(value,2);
    if(k<fields.length-1)value=projection(value,1);
    const type=name===hom?homType(A,B):isoType(A,B);
    declare(`${name}.${field.name}`,explicit(header([A,B],true),[[f,type]]),typeOf(field),value,"projection",{field:field.name});
  });
  const ownType=field=>fieldType(field,sort=>reference(bound(maps.get(sort))));
  declare(hom,modelParams(),null,sigma(homFields,ownType),"hom",{fields:homFields,parents:record.parents});
  declare(`${hom}.make`,explicit(modelParams(),homFields.map(field=>[bound(field),ownType(field),field.name])),
    homType(A,B),tuple(homFields.map(field=>reference(bound(field)))),"make");
  const fHom=sided(reference(f),A,B),gHom=sided(reference(g),B,C);
  projections(hom,homFields,field=>fieldType(field,sort=>mapping(fHom,sort)));
  const oneModel=()=>explicit(header([A]),[[A,modelType(A)]]);
  declare(`${hom}.id`,oneModel(),homType(A,A),apply(decl(`${hom}.make`),[reference(A),reference(A),...homFields.map(field=>{
    if(field.sort)return memberBody(field.sort,side(A),x=>x);
    const op=field.operation,step={from:side(A),to:side(A)};
    return bind(op.inputs,(input,locals)=>inputType(input,step,locals),locals=>
      built("refl",[apply(projected(op.id,A),op.inputs.map(input=>locals.get(input.id)))]),"lambda");
  })],implicitArgs([A,A],false)),"id");
  declare(`${hom}.compose`,explicit(header([A,B,C],true),[[g,homType(B,C)],[f,homType(A,B)]]),homType(A,C),
    apply(decl(`${hom}.make`),[reference(A),reference(C),...homFields.map(field=>{
      const viaF=sort=>mapping(fHom,sort),viaG=sort=>mapping(gHom,sort);
      const first=along(side(A),side(B),viaF),second=along(first.to,side(C),viaG);
      if(field.sort)return memberBody(field.sort,side(A),(x,locals)=>mapped(viaG(field.sort),field.sort,first.to,
        mapped(viaF(field.sort),field.sort,side(A),x,locals),locals));
      const op=field.operation,outer={from:side(A),to:side(C)},pulledBack=along(side(B),side(C),viaG);
      return bind(op.inputs,(input,locals)=>inputType(input,outer,locals),locals=>{
        const fAt=apply(project(hom,field.name,fHom),op.inputs.map(input=>input.way==="pull"
          ?pull(input.shape,locals.get(input.id),pulledBack,locals):locals.get(input.id)));
        const gAt=apply(project(hom,field.name,gHom),op.inputs.map(input=>input.way==="push"
          ?push(input.shape,locals.get(input.id),first,locals):locals.get(input.id)));
        const image=local("image"),carried=op.result.way==="fixed"?fAt:built("cong",[
          lambda(image,typeAt(op.result.shape,first.to,locals),push(op.result.shape,reference(image),second,locals)),fAt]);
        return built("trans",[carried,gAt]);
      },"lambda");
    })],implicitArgs([A,C],false)),"compose");
  for(const parent of record.parents) {
    const parentModel=model=>apply(ref(parent.projectionId),[reference(model)]);
    const fields=parent.fieldIds.flatMap((id,k)=>parent.kinds[k]==="sort"?[maps.get(id)]
      :parent.kinds[k]==="operation"?[homFields.find(field=>field.operation?.id===id)]:[]);
    declare(`${hom}.${parent.label}`,explicit(header([A,B],true),[[f,homType(A,B)]]),
      apply(ref(parent.homId),[parentModel(A),parentModel(B)]),
      apply(ref(parent.homMakeId),[parentModel(A),parentModel(B),...fields.map(field=>project(hom,field.name,fHom))]),
      "projection",{field:parent.label});
  }
  if(plan.isoSupport.status==="conditional") {
    const isoFieldType=(field,to,from)=>{
      if(field.name==="to")return homType(A,B);
      if(field.name==="from")return homType(B,A);
      const start=side(field.way==="from_to"?A:B),[first,second]=field.way==="from_to"?[to,from]:[from,to];
      return memberBody(field.sort,start,(x,locals)=>binary("=",mapped(mapping(second,field.sort),field.sort,start,
        mapped(mapping(first,field.sort),field.sort,start,x,locals),locals),x),"forall");
    };
    const toHom=sided(reference(bound(isoFields[0])),A,B),fromHom=sided(reference(bound(isoFields[1])),B,A);
    const fIso=sided(reference(f),A,B),gIso=sided(reference(g),B,C);
    declare(iso,modelParams(),null,sigma(isoFields,field=>isoFieldType(field,toHom,fromHom)),"iso",{fields:isoFields});
    declare(`${iso}.make`,explicit(modelParams(),isoFields.map(field=>[bound(field),isoFieldType(field,toHom,fromHom),field.name])),
      isoType(A,B),tuple(isoFields.map(field=>reference(bound(field)))),"make");
    projections(iso,isoFields,field=>isoFieldType(field,there(fIso),back(fIso)));
    const identity=apply(decl(`${hom}.id`),[reference(A)],implicitArgs([A],false));
    declare(`${iso}.id`,oneModel(),isoType(A,A),apply(decl(`${iso}.make`),[reference(A),reference(A),identity,identity,
      ...isoFields.slice(2).map(field=>memberBody(field.sort,side(A),x=>built("refl",[x])))],implicitArgs([A,A],false)),"id");
    const roundTrip=field=>{
      const [start,middle,inner,outer]=field.way==="from_to"?[side(A),side(B),gIso,fIso]:[side(C),side(B),fIso,gIso];
      const [away,home]=field.way==="from_to"?[there(outer),back(outer)]:[back(outer),there(outer)];
      return memberBody(field.sort,start,(x,locals)=>{
        const image=local("image"),inside=mapped(mapping(away,field.sort),field.sort,start,x,locals);
        const trip=(i,value)=>apply(project(iso,field.name,i),[...(families.get(field.sort)??[]).map(index=>locals.get(index.id)),value]);
        return built("trans",[built("cong",[lambda(image,typeAt(member(field.sort),middle,locals),
          mapped(mapping(home,field.sort),field.sort,start,reference(image),locals)),trip(inner,inside)]),trip(outer,x)]);
      });
    };
    const compose=(models,g,f)=>apply(decl(`${hom}.compose`),[g.value,f.value],implicitArgs(models));
    declare(`${iso}.compose`,explicit(header([A,B,C],true),[[g,isoType(B,C)],[f,isoType(A,B)]]),isoType(A,C),
      apply(decl(`${iso}.make`),[reference(A),reference(C),compose([A,B,C],there(gIso),there(fIso)),
        compose([C,B,A],back(fIso),back(gIso)),...isoFields.slice(2).map(roundTrip)],implicitArgs([A,C],false)),"compose");
    declare(`${iso}.inverse`,explicit(header([A,B],true),[[f,isoType(A,B)]]),isoType(B,A),
      apply(decl(`${iso}.make`),[reference(B),reference(A),back(fIso).value,there(fIso).value,...isoFields.slice(2).map(field=>
        project(iso,isoFields.find(other=>other.sort===field.sort&&other.way!==field.way).name,fIso))],implicitArgs([B,A],false)),"inverse");
  }
  return {plan,artifacts,bindings,record:{...record,...support,homId:bindings.get(hom).id,homMakeId:bindings.get(`${hom}.make`).id}};
}
