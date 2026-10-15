// Equational initial/free artifacts consume an explicit checked application
// interface. Field syntax and caller arguments already have identities; this
// builder never resolves them in the generated declaration's environment.
import {bindingResolution,reservedResolution,expandedOrigin} from "./bindings.mjs";
import {bindingSyntaxView,cloneBindingSyntax,substituteBindingSyntax} from "./binding-syntax.mjs";
import {freshName,unlinked,relocated} from "./scopes.mjs";

const at=origin=>({start:origin.start,end:origin.end,origin,synthetic:true});
const token=binding=>({text:binding.label,bindingId:binding.id,bindingRole:binding.role,...at(binding.origin)});
const reference=binding=>({kind:"bindingReference",resolution:bindingResolution(binding.id),spelling:binding.label,...at(binding.origin)});
const builtin=(label,origin)=>({kind:"bindingReference",resolution:reservedResolution(label),spelling:label,...at(origin)});

// `given` maps the theory's complete header to arguments checked together in
// the request header. Solved core arguments may be inert `instantiated` nodes
// abstracted over that header; no checking scope or live kernel handle enters
// this API. The conditional support plan describes construction, not proof:
// every resulting declaration still needs normal admission and publication.
export function retainedInitialArtifacts(record,request,{table,owner,plan}) {
  const {header,given,generator=null,binding,origin=binding.origin}=request;
  if(!record.bindingSyntax||header?.tree.kind!=="def"||!(given instanceof Map)
    ||binding.role!=="declaration"||plan?.strategy!=="equational")
    throw new TypeError("An equational artifact needs retained interfaces and an explicit application plan.");
  if(plan.status!=="conditional")return {plan,artifacts:[],bindings:new Map()};
  const headerIds=[...record.universeIds,...record.params.map(p=>p.id)];
  if(given.size!==headerIds.length||headerIds.some(id=>!given.has(id)))
    throw new TypeError("An equational artifact needs the complete theory argument correspondence.");
  const N=binding.label,free=generator!==null,view=tree=>bindingSyntaxView(header,tree);
  const call=(fn,args)=>args.length?{kind:"call",fn,args,...at(origin)}:fn;
  const named=(label,value)=>({kind:"namedArgument",name:{text:label,...at(origin)},value,...at(origin)});
  const hole=()=>({kind:"name",name:"_",...at(origin)});
  const fields=new Map(record.fields.map(f=>[f.id,f]));
  const carrier=fields.get(plan.mapping.carrier),evidence=fields.get(plan.mapping.evidence);
  if(!carrier||!evidence)throw new TypeError("An equational plan names an unknown carrier or evidence identity.");
  const shapes=plan.mapping.constructors.map(shape=>({...shape,field:fields.get(shape.id)}));
  if(shapes.some(shape=>!shape.field))throw new TypeError("An equational plan names an unknown field identity.");
  const labels=[N,`${N}.model`,`${N}.fold_map`,`${N}.fold`,...(free?[`${N}.gen`]:[]),
    ...shapes.map(shape=>`${N}.${shape.field.name}`)];
  if(new Set(labels).size!==labels.length)throw new TypeError("Generated declaration labels must be distinct.");
  const bindings=new Map([[N,table.get(binding.id)]]);
  for(const label of labels.slice(1))bindings.set(label,table.allocate([...owner,"declarations"],{role:"declaration",label,origin}));
  const declared=suffix=>bindings.get(`${N}.${suffix}`);
  const taken=new Set(header.tree.params.map(p=>p.name.text));
  const local=(stem,source=origin,role="local")=>table.allocate([...owner,"locals"],
    {role,label:freshName(stem,taken),origin:expandedOrigin(source,{kind:"generation",site:origin})});
  const params=header.tree.params,arguments_=params.map(p=>reference(table.get(p.name.bindingId)));
  const self=()=>call(reference(binding),arguments_);
  const ownModel=()=>call(reference(declared("model")),arguments_);
  let serial=0;
  const substitute=(tree,map)=>relocated(substituteBindingSyntax(view(tree),map,table,[...owner,"substitution",String(serial++)]).tree,at(origin));
  const universe=substitute(carrier.type,given);
  const theory=call(reference(table.get(record.modelId)),headerIds.map(id=>given.get(id).tree));
  const inside=new Map([...given,[carrier.id,view(self())],
    ...shapes.filter(shape=>shape.kind==="operation").map(shape=>[shape.id,view(reference(declared(shape.field.name)))])]);
  const constructors=shapes.map(shape=>{
    const correspondence=new Map(inside),names=new Set(),parameters=[];
    for(const argument of shape.arguments) {
      // Flattening nested quantifiers preserves each identity. Distinct
      // printable labels also preserve the constructor's argument interface.
      const label=freshName(argument.name,names),field=table.allocate([...owner,"constructor",shape.field.name],
        {role:"parameter",label,origin:table.get(argument.id).origin});
      const type=substitute(argument.type,correspondence);
      parameters.push({name:{...token(field),label:argument.name},label:argument.name,type,group:argument.group});
      correspondence.set(argument.id,view(reference(field)));
    }
    return {kind:"constructor",name:token(declared(shape.field.name)),params:parameters,
      type:shape.kind==="law"?substitute(shape.body,correspondence):null,...at(origin)};
  });
  if(free) {
    const item=local("a");
    constructors.unshift({kind:"constructor",name:token(declared("gen")),
      params:[{name:token(item),type:generator.tree,group:0}],type:null,...at(origin)});
  }
  const generated={initial:N},artifacts=[];
  const emit=(binding,tree,metadata=generated)=>{
    const syntax=cloneBindingSyntax(view(artifacts.length?{...tree,params:unlinked(tree.params)}:tree),table,[...owner,"artifact",String(artifacts.length)],
      {expansion:{kind:"generation",site:origin}}).syntax;
    artifacts.push({binding,syntax,generated:metadata});
  };
  emit(binding,{kind:"inductive",name:token(binding),params,
    result:{modifier:{kind:evidence.evidence==="IsSet"?"set":"prop",...at(origin)},universe},constructors,...at(origin)},
  {...generated,laws:Object.fromEntries(shapes.filter(s=>s.kind==="law").map(s=>[declared(s.field.name).label,s.field.name])),
    theorySpan:request.theorySpan??at(origin),...(free?{generatorSpan:request.generatorSpan??at(origin)}:{})});

  const nextGroup=1+Math.max(-1,...params.map(p=>p.group??0));
  const define=(suffix,extra,type,value)=>emit(declared(suffix),{kind:"def",name:token(declared(suffix)),
    params:[...params,...extra.map(([binding,type],k)=>({name:token(binding),type,group:nextGroup+k}))],
    type,body:[{kind:"exact",value,...at(origin)}],typedValue:true,...at(origin)});
  const lambdas=(bindings,body)=>bindings.reduceRight((body,binding)=>({kind:"lambda",name:token(binding),body,...at(origin)}),body);
  const target=local("target"),proof=local("evidence"),g=local("g"),x=local("x");
  const projected=field=>call(reference(table.get(field.projectionId)),[reference(target)]);
  const generatorParam=free?[[g,{kind:"binary",operator:"->",left:unlinked(generator.tree),right:projected(carrier),...at(origin)}]]:[];
  const recurse=(evidence,value)=>call(reference(declared("fold_map")),[...arguments_,reference(target),evidence,
    ...(free?[reference(g)]:[]),value]);
  const mapped=(shape,variables,evidence)=>shape.arguments.map((argument,k)=>argument.action==="recurse"
    ?recurse(evidence,reference(variables[k])):reference(variables[k]));
  const variables=shape=>shape.arguments.map(argument=>local(argument.name,table.get(argument.id).origin));
  define("model",[],header.tree.type,call(reference(table.get(record.makeId)),[
    ...record.params.map(p=>given.get(p.id).tree),named(carrier.name,self()),named(evidence.name,hole()),
    ...shapes.map(shape=>{
      const args=variables(shape);
      return named(shape.field.name,lambdas(args,call(reference(declared(shape.field.name)),args.map(reference))));
    })]));
  const clause=(constructor,variables,value,dimension=null)=>({kind:"clause",constructor:token(constructor),
    args:variables.map(token),binders:[],coordinates:dimension?[token(dimension)]:[],body:value,...at(origin)});
  const clauses=shapes.map(shape=>{
    const args=variables(shape),applied=call(projected(shape.field),mapped(shape,args,reference(proof)));
    const dimension=shape.kind==="law"?local("i",origin,"dimension"):null;
    return clause(declared(shape.field.name),args,dimension?{kind:"pathApply",operator:"@",left:applied,
      right:reference(dimension),...at(origin)}:applied,dimension);
  });
  if(free) {
    const a=local("a");clauses.unshift(clause(declared("gen"),[a],call(reference(g),[reference(a)])));
  }
  // The evidence predicate is itself captured source syntax. Instantiate
  // the full evidence type, including universe and carrier correspondence.
  const targetFields=new Map([...given,...record.fields.map(field=>[field.id,view(projected(field))])]);
  define("fold_map",[[target,theory],[proof,substitute(evidence.type,targetFields)],...generatorParam,[x,self()]],projected(carrier),
    {kind:"match",value:reference(x),motiveName:null,type:null,clauses,...at(origin)});
  define("fold",[[target,theory],...generatorParam],call(reference(table.get(record.homId)),[ownModel(),reference(target)]),
    call(reference(table.get(record.homMakeId)),[ownModel(),reference(target),
      named("map",lambdas([x],recurse(projected(evidence),reference(x)))),
      ...shapes.filter(shape=>shape.kind==="operation").map(shape=>{
        const args=variables(shape);
        return named(`map_${shape.field.name}`,lambdas(args,call(builtin("refl",origin),[
          call(projected(shape.field),mapped(shape,args,projected(evidence)))])));
      })]));
  return {plan,artifacts,bindings};
}
