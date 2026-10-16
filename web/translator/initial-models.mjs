// L2.6's retained construction-and-fold prototype. This does not register
// an initial/free capability: deriving and the universal proofs are pending.
// The expansion is ordinary syntax, checked with no new kernel rule.
import {propagateElaborationStop} from "./control.mjs";
import {failedExpansion} from "./theories.mjs";
import {assignArguments} from "./arguments.mjs";
import {Scope} from "./elaboration.mjs";
import {T as Term} from "./core.mjs";
import {DependencyAnalysis,dependencyUses} from "../cubist/dependencies.mjs";
import {bindingSyntaxView,bindingUses,unresolvedBindingUse,resolveBindingSyntax} from "../cubist/binding-syntax.mjs";

import {bindingResolution,sourceOrigin} from "../cubist/bindings.mjs";
import {retainedInitialArtifacts} from "../cubist/retained-initial-artifacts.mjs";
import {bindingDeclaration,lowerBindingDeclaration} from "./binding-module.mjs";
import {enterSourceItem} from "./retained-source-context.mjs";
import {repeatedName} from "./names.mjs";

// This strategy shares exact dependency facts with Hom planning, not its
// admissibility predicate. A constructor argument is a carrier value or a
// type independent of carrier values/proofs; arbitrary variance is not enough.
export function equationalSupport(record) {
  if(!record.bindingSyntax)throw new TypeError("Equational dependency planning needs retained binding interfaces.");
  const view=tree=>bindingSyntaxView(record.bindingSyntax,tree);
  const reference=node=>node?.kind==="bindingReference"&&node.resolution.tag==="binding"?node.resolution.id:null;
  const analysis=new DependencyAnalysis([...record.fields,...record.derived??[]]);
  const pending=record.fields.flatMap(field=>dependencyUses(view(field.type))
    .filter(unresolvedBindingUse).map(use=>({field:field.id,...use})));
  if(pending.length)return {status:"pending",strategy:"equational",obligations:pending};
  const origin=record.fields[0]?.binding?.origin;
  const refuse=(error,at=origin,detail={})=>({status:"unsupported",strategy:"equational",reason:error.message,at,...detail});
  const carriers=record.fields.filter(field=>field.kind==="sort");
  if(carriers.length!==1||carriers[0].family)return refuse(notOneCarrier(record.name,carriers));
  const carrier=carriers[0],evidence=record.fields.find(field=>field.kind==="evidence"&&field.of===carrier.id);
  if(!evidence)return refuse(untruncatedCarrier(record.name,carrier.name));
  const mapping=[];
  for(const field of record.fields) {
    if(["sort","evidence"].includes(field.kind))continue;
    const recursive=new Map(),args=[];
    let body=field.type,group=0,refusal=null;
    while(body.kind==="forall"||body.kind==="binderGroup"&&body.binderKind==="forall") {
      const names=body.kind==="forall"?[body.name]:body.names;
      if(body.bound)return refuse(universeArguments(field.name),names[0].origin,{field:field.id});
      const domain=body.domain,isCarrier=reference(domain)===carrier.id;
      if(!isCarrier) {
        const dependencies=analysis.dependencies(view(domain),{conditional:true});
        const dependency=dependencies.find(use=>["law","evidence"].includes(use.category))
          ??dependencies.find(use=>["carrier","operation","helper","recursive-helper"].includes(use.category));
        const local=dependencyUses(view(domain)).find(use=>use.kind==="binding"&&recursive.has(use.id));
        if(dependency||local) {
          const use=dependency??local,proof=["law","evidence"].includes(use.category);
          const label=analysis.byIdentity.get(use.id)?.label??recursive.get(use.id)?.label;
          refusal??=refuse(proof?onProof(field.name,names[0].label??names[0].text,use.category,label)
            :notPositive(field.name,names[0].label??names[0].text,carrier.name),use.origin,{field:field.id,dependency:use});
        }
      }
      for(const token of names) {
        if(!token.bindingId)throw new TypeError("An equational constructor telescope needs binding identities.");
        args.push({id:token.bindingId,name:token.label??token.text,action:isCarrier?"recurse":"fixed",type:domain,group});
        if(isCarrier)recursive.set(token.bindingId,{label:token.label??token.text});
      }
      body=body.body;group++;
    }
    if(field.kind==="law"&&(!(body.kind==="binary"&&body.operator==="=")
      ||analysis.first(view(body),["law","evidence"],{conditional:true})))
      return refuse(notEquational(field.name),body.origin??field.binding.origin,{field:field.id});
    if(refusal)return refusal;
    if(field.kind==="operation") {
      if(body.kind==="binary"&&body.operator==="->")return refuse(arrowOperation(field.name),body.origin??field.binding.origin,{field:field.id});
      if(reference(body)!==carrier.id)return refuse(notCarrierValued(field.name,carrier.name),body.origin??field.binding.origin,{field:field.id});
    }
    mapping.push({id:field.id,kind:field.kind,arguments:args,body});
  }
  return {status:"conditional",strategy:"equational",mapping:{carrier:carrier.id,evidence:evidence.id,constructors:mapping},
    obligations:["interfaces","universes","positivity","boundaries","model","fold","preservation"]
      .map(kind=>({kind,strategy:"equational",theory:record.name}))};
}

// The declarations an initial or free model expands to, checked in its
// place; one that does not expand fails as a declaration of its name.
export function initialDeclarations(t, module, d, env, declarations) {
  const unit = module.declaration(t.declarationFuel).with({references: null});
  try {
    return retainedInitialSource(t,unit,d,env);
  }
  catch (failure) {propagateElaborationStop(failure); return failedExpansion(t, d, env, declarations, unit.locate(failure, d.name)); }
  finally { unit.fuel.close(); }
}

function retainedInitialSource(t,module,declaration,env) {
  const owner=["initial-source",module.moduleName,String(declaration.start)];
  const {table,source,inputs,prepared,captures}=enterSourceItem(t,module,declaration,env,owner);
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
  {table,owner:[...owner,"header"],source,context:prepared.context,constructors:inputs.constructors,simpSets:inputs.simpSets,
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

// Check the whole application once under its complete caller telescope.
// Return inert core arguments abstracted over that telescope. The retained
// builder supplies its own references when instantiating them
// in each generated declaration. In particular, solved holes are not solved
// again independently in copied field types.
export function checkedInitialArguments(t,module,{theory,params,parameters,env,name,at=theory}) {
  const args=theory.kind==="call"?theory.args:[];
  const argument=assignArguments({...theory,args},parameters,module,name);
  if(args.length!==parameters.length)
    throw module.locate(theoryArguments(name,parameters.length,args.length),theory);
  const place={start:at.start,end:at.end,...(at.origin?{origin:at.origin}:{}),...(at.synthetic?{synthetic:true}:{})};
  // Assignment has already selected exact positions. Converting those back
  // to names would merge anonymous positions that share the public label _.
  let checked=args.length?{...theory,args:parameters.map((_,k)=>argument(k)),checkArguments:true}:theory;
  for(let k=params.length-1;k>=0;) {
    const group=params[k].group,members=[];
    while(k>=0&&params[k].group===group)members.unshift(params[k--]);
    checked={kind:"binderGroup",binderKind:"lambda",names:members.map(p=>p.name),
      ...(members[0].bound?{bound:members[0].bound}:{domain:members[0].type}),body:checked,...place};
  }
  const scope=new Scope(module,new Map(),env);
  const application=t.term(checked,scope);
  scope.infer(application);
  const telescope=[],values=[];
  let applied=application;
  for(let k=0;k<params.length;k++){telescope.push(applied);applied=applied.body;}
  for(let k=parameters.length-1;k>=0;k--) {
    const value=applied.tag==="LApp"?Term.universe(applied.level):applied.arg;
    values[k]=telescope.reduceRight((body,binder)=>({...binder,body}),value);
    applied=applied.fn;
  }
  return values;
}

// The strategy's refusal of a law whose path constructor the kernel refuses
// as a boundary (K102-K105, K133-K140), as one whose side is a match, or
// null for any other failure, which keeps the kernel's own message.
const BOUNDARY = /: A (?:constructor's boundary|boundary|binder(?:'s type)? in a boundary|path abstraction or application in a boundary)\b/;
export const lawRefusal = (d, failure) => {
  const law = d.generated?.laws?.[failure.constructor];
  return law && BOUNDARY.test(failure.message ?? "") ? notEquational(law) : null;
};

// Explain failures of generated constructors at the expression the user
// wrote, without exposing the generator constructor's synthetic argument.
export function initialRefusal(d, failure) {
  const N = d.generated?.initial;
  if (d.generated?.generatorSpan && failure.dataUniverse?.constructor === `${N}.gen`)
    return {error: Object.assign(generatorUniverse(N), {kind: failure.kind}), at: d.generated.generatorSpan};
  const law = lawRefusal(d, failure);
  return law ? {error: law, at: d.generated.theorySpan} : null;
}

// Refusals describe this strategy's limits, not nonexistence of a model.
export const notATheory = (kind, given) => Error(`${kind} takes a theory at its universes and parameters, as ${
  kind === "free" ? "free W(A : U0) : Monoid(U0) on A" : "initial N : Monoid(U0)"}; ${given} is none.`);
const theoryArguments = (T, wanted, given) => Error(`${T} takes ${wanted} argument${wanted === 1 ? "" : "s"}, its universes and parameters; this gives ${given}.`);
const notOneCarrier = (T, carriers) => Error(`The equational strategy supports one carrier that is not a family; ${T} has ${
  carriers.length ? carriers.map(f => f.family ? `the family ${f.name}` : f.name).join(", ") : "none"}.`);
const untruncatedCarrier = (T, carrier) => Error(`${T}'s carrier ${carrier} is neither a set nor a proposition: the equational strategy requires a truncated carrier.`);
const notPositive = (field, binder, carrier) => Error(`${field} takes ${binder} with a type depending on the carrier ${carrier}: the equational strategy supports carrier arguments or types independent of the carrier.`);
const onProof = (field, binder, kind, proof) => Error(`${field} takes ${binder} with a type depending on the ${kind} ${proof}: the equational strategy supports arguments independent of the theory's laws and carrier evidence.`);
const notCarrierValued = (field, carrier) => Error(`${field} does not return the carrier ${carrier}: the equational strategy supports carrier-valued operations.`);
const notEquational = field => Error(`The law ${field} is not an equation between operation terms: the equational strategy does not support this law.`);
const arrowOperation = field => Error(`${field} uses an arrow type: the equational strategy requires named operation arguments, as in succ(x : M) : M.`);
export const recursiveGenerators = N => Error(`The generator type of ${N} mentions ${N} or one of its generated names: free requires a type given independently of the declared model.`);
const generatorUniverse = N => Error(`The generator type of ${N} lives in a universe above its carrier's declared one: a free model cannot lower its generators. Choose a larger carrier universe or a smaller generator type.`);
const universeArguments = field => Error(`${field} binds a universe argument: the equational strategy supports term arguments only; bind universes in the theory header.`);
