// Ordered source retention for the explicit theory-interface family. The
// declaration builders consume this record, never a reconstructed source
// declaration. Deferred selections/notation and inheritance enter through
// their own source-scope boundaries as those families migrate.
import {RetainedInterfaces} from "./retained-interfaces.mjs";
import {HelperExpansion} from "./helper-expansion.mjs";
import {bindingSyntaxView} from "./binding-syntax.mjs";
import {bindingResolution,reservedResolution,sourceOrigin} from "./bindings.mjs";
import {evidenceLayout,parameterGroup} from "./telescopes.mjs";
import {allNames,freeNames,freshName,scopeMapped} from "./scopes.mjs";
import {notAProposition,retainedPropositionSymbols} from "./theory-propositions.mjs";
import {retainParents} from "./retained-parents.mjs";
import {retainFieldNotation} from "./retained-notation.mjs";

const located=(error,node)=>Object.assign(error,{offset:node.start,sourceEnd:node.end});
const reference=token=>({kind:"bindingReference",resolution:bindingResolution(token.bindingId),
  spelling:token.text,origin:token.origin,start:token.start,end:token.end});

// An implicit family-evidence argument is selected by its carrier binder's
// identity. The complete parameter telescope already owns both binders, so
// a later same-labelled parameter cannot change which evidence is supplied.
function familyEvidence(syntax,families) {
  const evidence=new Map();
  for(const parameter of syntax.tree.params)if(parameter.level) {
    const witness=syntax.tree.params.find(p=>p.name.synthetic&&p.type?.kind==="call"
      &&p.type.args[1]?.kind==="bindingReference"&&p.type.args[1].resolution.tag==="binding"
      &&p.type.args[1].resolution.id===parameter.name.bindingId);
    if(!witness)throw new TypeError("A leveled interface parameter has no retained evidence binder.");
    evidence.set(parameter.name.bindingId,{level:parameter.level,token:witness.name});
  }
  const map=tree=>scopeMapped(tree,{deferred:true,extend:at=>at,enter(node) {
    if(node.kind!=="call"||node.fn.kind!=="bindingReference"||node.fn.resolution.tag!=="binding")return node;
    const family=families.get(node.fn.resolution.id);
    if(!family?.visible.some(Boolean)||node.args.length!==family.visible.length)return node;
    const supplied=node.args.map(map),args=evidenceLayout(family.visible.map(level=>({level}))).map(({kind,index,level})=>{
      const source=node.args[index],arg=supplied[index];
      if(kind==="argument")return arg;
      const witness=arg.kind==="bindingReference"&&arg.resolution.tag==="binding"?evidence.get(arg.resolution.id):null;
      if(witness?.level!==level)throw located(Error(`${family.label}'s argument ${index+1} is a ${level==="set"?"set":"proposition"} with its evidence: give an index bound as one, (A : ${level} U), or write its evidence after it, ${family.label}(…, A, A_is_${level}, …).`),source);
      return reference(witness.token);
    });
    return {...node,args};
  }},null);
  return bindingSyntaxView(syntax,map(syntax.tree),{inferred:syntax.inferred});
}

export function retainTheorySource(theory,options,{proposition=()=>false,lookup=()=>null}={}) {
  if(theory.kind!=="theory")throw new TypeError("Theory retention requires a parsed theory declaration.");
  if(theory.uses?.length)
    throw new TypeError("Retained theory source selections must be activated before retention.");
  const T=theory.name.text,interfaces=new RetainedInterfaces(options),taken=new Set(allNames(theory));
  const origin=sourceOrigin({...options.source,start:theory.name.start,end:theory.name.end});
  const generatedUniverse=!theory.universes.length;
  // The public theory interface puts universes first, retaining the written
  // groups and their shared bounds. The flattened list of universe labels
  // cannot reconstruct those source regions.
  const universes=generatedUniverse?parameterGroup([
    {text:freshName("U",taken),start:origin.start,end:origin.end,synthetic:true}],
    {bound:{kind:"name",name:"UU0",start:origin.start,end:origin.end}},-1):theory.header.filter(p=>p.bound);
  const params=[...universes,...theory.params];
  if(generatedUniverse)params[0].label=freshName("U",new Set(theory.params.map(p=>p.name.text)));
  const headerNames=new Set();
  for(const parameter of params) {
    if(parameter.name.text==="_")continue;
    if(headerNames.has(parameter.name.text))throw located(Error(`${T}'s header binds ${parameter.name.text} twice: give each its own name.`),parameter.name);
    headerNames.add(parameter.name.text);
  }
  const header=interfaces.parameters(theory.name,params,{fixedReferences:new Map(params.filter(p=>p.bound)
    .map(p=>[p.bound,reservedResolution("UU0")]))}),families=new Map(),fields=[],derived=[];
  const byName=new Map(),byIdentity=new Map(),notationBindings={};
  const admit=(entry,metadata={})=>{
    if(byName.has(entry.label))throw located(Error(`${T} has two fields named ${entry.label}: give each its own name.`),entry.binding.origin);
    if(entry.kind!=="derived"&&headerNames.has(entry.label))
      throw located(Error(`${T}'s header binds ${entry.label}, which names a field too: give each its own name.`),entry.binding.origin);
    const full=Object.freeze({...entry,name:entry.label,...metadata});
    byName.set(entry.label,full);byIdentity.set(entry.id,full);
    (entry.kind==="derived"?derived:fields).push(full);
    return full;
  };
  const {parents,ambiguous}=retainParents(theory,interfaces,{...options,lookup},admit);
  if(parents.length) {
    const helpers=new HelperExpansion(interfaces.entries,{table:options.table,owner:[...options.owner,"inherited-views"]});
    for(const entry of fields) {
      byIdentity.set(entry.id,{...entry,type:helpers.type(entry).analysis.tree});
      if(entry.visible)families.set(entry.id,entry);
    }
  }
  for(const item of theory.fields) {
    const self=item.kind==="derived"&&freeNames(item.value,new Set(item.params.map(p=>p.name.text))).has(item.name.text);
    const {notation,...plain}=item;
    const entry=interfaces.retain(plain,{self,transform:syntax=>familyEvidence(syntax,families)});
    const metadata={...(item.kind==="sort"&&item.params.length?{family:true}:{}),
      ...(item.params.some(p=>p.level)?{visible:item.params.map(p=>p.level??null)}:{})};
    const full=admit(entry,metadata);
    const retainedNotation=retainFieldNotation(item,entry,fields,{...options,theory:T});
    if(retainedNotation) {
      const previous=notationBindings[retainedNotation.key];
      if(previous&&previous.field!==entry.id)
        throw located(Error(`${retainedNotation.key} would stand for both ${options.table.get(previous.field).label} and ${entry.label} in ${T}: a notation means one operation; rename one's notation.`),notation);
      notationBindings[retainedNotation.key]=retainedNotation;
    }
    if(item.kind==="derived")continue;
    if(full.visible)families.set(entry.id,full);
    const helpers=new HelperExpansion(interfaces.entries,{table:options.table,owner:[...options.owner,"validate",String(fields.length)]});
    const signature=helpers.signature(entry);
    if(signature.recursive) {
      const use=signature.recursive,label=byIdentity.get(use.id)?.label??use.spelling;
      throw located(Error(`${label} is recursive, and a field's type cannot unfold it: state the law over a model, outside the theory.`),use.origin??item);
    }
    const views=helpers.type(entry);
    // Shape facts are conditional on the complete checking view, which the
    // artifact builder puts in the base publication group's declarations.
    byIdentity.set(entry.id,{...full,type:views.analysis.tree});
    if(item.kind==="law") {
      const data=notAProposition(views.analysis.tree,byIdentity,proposition,
        header.tree.params.map(p=>p.name.bindingId),retainedPropositionSymbols);
      if(data)throw located(Error(`The law ${item.name.text} must state a proposition: an equation between elements of a sort, Void, a type declared at prop, or forall, -> or and over those; ${data.why}. A law holds no data, and homomorphisms ignore laws: declare data as an operation or a constant.`),data.node.origin??data.node);
    }
    if(item.kind==="sort") {
      if(item.level)admit(interfaces.evidence(entry));
    }
  }
  if(!fields.length)throw located(Error(`${T} has no fields: a theory declares sorts, operations and laws.`),theory.name);
  for(const parent of parents)if(byName.has(parent.label))
    throw located(Error(`${T}'s parent ${parent.theory} is labelled ${parent.label}, which names a field of ${T} too: label it apart, as in base : ${parent.theory}.`),theory.name);
  return {name:T,origin,bindingSyntax:header,entries:interfaces.entries.map(entry=>byName.get(entry.label)),fields,derived,parents,
    notationBindings:Object.freeze(notationBindings),
    notations:Object.fromEntries(Object.entries(notationBindings).map(([key,value])=>[key,options.table.get(value.field).label])),
    ambiguous:Object.fromEntries(ambiguous),
    ...(generatedUniverse?{generatedUniverse:true}:{})};
}
