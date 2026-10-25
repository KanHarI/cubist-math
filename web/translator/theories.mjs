// Theories in elaboration (L2.4, docs/roadmaps/high-level-abstractions/core-theories.md): a theory
// declaration's retained expansion and the records it
// leaves, by which m.f reads a field of a model m and `open m;` puts a
// model's fields and notation in scope.
import {propagateElaborationStop} from "./control.mjs";
import {referenceKey, sourceName} from "../cubist/references.mjs";
import {Scope} from "./elaboration.mjs";
import {selectionEffects,fileSelectionEffects} from "../cubist/scopes.mjs";
import {substituteTerm,alphaKey,isTerm} from "./core.mjs";
import {failureRoot,untranslated,sourceFailure} from "./declarations.mjs";
import {projectedResolution,failedResolution} from "../cubist/bindings.mjs";
import {modelNotations,modelOperandRecipes,recordOf,notationAlternative,notationPrintingRecipe} from "./model-notation.mjs";
export {recordOf} from "./model-notation.mjs";
import {operatorBinding,SELECTION,bindNotationContext} from "./notation-context.mjs";
import {retainedNotationReceipt,registerRetainedNotationPrinting,retainSourceNotation} from "./named-notation.mjs";
import {lowerBindingReference} from "../cubist/binding-syntax.mjs";
import {retainedTheoryDeclarations} from "./retained-theories.mjs";
export {operatorBinding,SELECTION} from "./notation-context.mjs";

// The environment's key for a theory's record. The theory's name is its type
// of models (L2.4c), a definition like any other.
export const theoryBinding = name => "\u0000theory " + name;
// The environment's key for a named notation's rules (L2.10a), and the
// scope's key for the selected notation: its name and the operators it
// binds. A selection is complete: an operator it does not bind is an error,
// never an earlier selection's or a function named add.
export const notationBinding = name => "\u0000notation " + name;
// A theory's records, by the binding of its type of models, and its
// projections, which print as m.f.
export function registerTheoryDeclaration(t,d) {
  const binding=t.bindingName(d.name.text);
  if(d.theory) {
    // The queue reserved the whole family before admission. Record exact
    // projection identities once here, independently of their availability.
    const identify=field=>{
      if(field.projectionId)return field;
      const key=t.bindingName(field.projection);
      const identity=t.compilationBindings.declaration(key)?.binding;
      if(!identity)throw new TypeError("A model interface needs reserved projection identities.");
      return {...field,projectionId:identity.id};
    };
    (t.checker.theories??=new Map()).set(binding,{...d.theory,
      fields:d.theory.fields.map(identify),derived:(d.theory.derived??[]).map(identify),
      parents:d.theory.parents.map(identify)});
  }
  if(d.generated?.role==="projection")(t.checker.theoryProjections??=new Map()).set(binding,d.generated.field);
  // A projection whose field a notation names prints with that operator
  // where its model is selected (L2.10d), each operand in its view.
  if(d.theory)for(const [operator,rule] of Object.entries(d.theory.notationBindings??{}))
    if(!["unary -","numeral"].includes(operator)) {
      const record=t.checker.theories.get(binding),field=[...record.fields,...record.derived].find(field=>field.id===rule.field);
      const projection=t.compilationBindings.table.get(field.projectionId).label;
      (t.checker.notationPrinting??=new Map()).set(t.bindingName(projection),
        [{operator,model:true,recipe:notationPrintingRecipe(rule.recipe)}]);
    }
}

// n.name is m.f: when m is a model of a theory, the node of the call T.f(m),
// or T.p(m) for a parent labelled p; otherwise null, or, where m is bound
// here and hides a declaration m.f, the error that says so.
export function modelField(t,scope,n) {
  const dot=n.name.lastIndexOf("."),first=dot>0?n.name.slice(0,n.name.indexOf(".")):null,root=first?scope.env.get(first):null;
  // A name under a theory's, T.Hom, is a qualified name, not a field. A
  // local model that shadows the theory's name is a model like any other.
  if(!root||theoryRoot(t,scope,first,root))return null;
  const spelling=n.spelling??n.name,writtenDot=spelling.lastIndexOf(".");
  const owner={...n,name:n.name.slice(0,dot),...(n.spelling?{spelling:spelling.slice(0,writtenDot)}:{}),end:n.start+writtenDot};
  const record=recordOf(t,scope,t.term(owner,scope,null));
  if(!record&&scope.hiding(n.name))throw Error(`${first} is bound here, which hides the declaration ${n.name}: rename the binding to refer to it.`);
  if(!record)return null;
  const field=n.name.slice(dot+1);
  const known=record.fields.find(f=>f.name===field)??record.derived?.find(d=>d.name===field)??record.parents.find(p=>p.label===field);
  if(!known&&record.ambiguous?.[field])throw ambiguousField(record,owner.name,field);
  if(!known)throw Error(`${owner.name} is a model of ${record.name}, which has no field ${field}: it has ${record.fields.map(f=>f.name).join(", ")}${
    record.parents.length?`, and the parents ${record.parents.map(p=>p.label).join(", ")}`:""}.`);
  return scope.declared({kind:"call",fn:projectionReference(t,known,n),args:[owner],start:n.start,end:n.end});
}

const projectionReference=(t,field,at)=>({...at,kind:"name",name:t.identityAdapter.key(field.projectionId),spelling:field.projection});

// A field that two independent parents give under one name (L2.4c): the
// error that names the qualified forms.
const ambiguousField=(record,model,field)=>Error(`${field} is ambiguous in ${record.name}: it is ${
  record.ambiguous[field].map(e=>`${e.label}'s`).join(" and ")}. Write ${record.ambiguous[field].map(e=>`${model}.${e.label}.${e.parentField}`).join(" or ")}.`);

// Whether `name`, bound to `root`, is the theory of that name: its type of
// models, or its declaration where that failed.
function theoryRoot(t,scope,name,root) {
  return scope.env.has(theoryBinding(name))&&(root.tag==="Untranslated"||root.tag==="DefRef"&&!!t.checker.theories?.has(root.name));
}

// e.f, for a value e that is not a name: when e is a model, the node of the
// call T.f(e); otherwise the error that says so.
export function memberField(t,scope,n) {
  const record=recordOf(t,scope,t.term(n.value,scope,null)),field=n.field.text;
  const receiver=sourceName(n.value),spelling=receiver&&`${receiver}.${field}`,key=referenceKey(n.value);
  if(!record) {
    if(spelling) {
      if(n.shadowedDeclaration)
        throw Error(`${n.shadowedDeclaration} is bound here, which hides the declaration ${spelling}: rename the binding to refer to it.`);
      if(n.value.kind==="name"&&!n.value.spelling&&scope.hiding(spelling))
        throw Error(`${scope.hiding(spelling)} is bound here, which hides the declaration ${spelling}: rename the binding to refer to it.`);
      const missing=key&&missingMorphisms(scope,`${key}.${field}`,spelling);
      if(missing)throw missing;
      if(field==="Model"&&key&&t.checker.theories?.has(scope.env.get(key)?.name))
        throw Error(`${receiver}.Model is now ${receiver}: a theory's name is the type of its models, as in ${receiver}(U0).`);
      throw Error(`Untranslated name: ${spelling}`);
    }
    throw Error(`.${field} reads a field of a model of a theory; this value is not one.`);
  }
  const known=record.fields.find(f=>f.name===field)??record.derived?.find(d=>d.name===field)??record.parents.find(p=>p.label===field);
  if(!known&&record.ambiguous?.[field])throw ambiguousField(record,receiver??"m",field);
  if(!known)throw receiver
    ? Error(`${receiver} is a model of ${record.name}, which has no field ${field}: it has ${record.fields.map(f=>f.name).join(", ")}${
      record.parents.length?`, and the parents ${record.parents.map(p=>p.label).join(", ")}`:""}.`)
    : Error(`This is a model of ${record.name}, which has no field ${field}: it has ${record.fields.map(f=>f.name).join(", ")}${
      record.parents.length?`, and the parents ${record.parents.map(p=>p.label).join(", ")}`:""}.`);
  return scope.declared({kind:"call",fn:projectionReference(t,known,{...n.field,...(n.synthetic?{synthetic:true}:{})}),args:[n.value],start:n.start,end:n.end,
    ...(n.origin?{origin:n.origin}:{}),...(n.synthetic?{synthetic:true}:{})});
}

// The scope with the model `node` opened, or null when it is no model: each
// field by its name, as its projection T.f(m), and each notation of the
// theory as m's operation. A later binding of a name or operator shadows it.
export function opened(t,scope,node,{complete=true,effects=selectionEffects.all,receiverScope=scope,
  receiver=t.term(node,receiverScope,null),activation=null}={}) {
  const checked=checkedOpening(t,scope,node,{complete,effects,receiverScope,receiver});
  return checked?openingScope(t,checked,node,activation):null;
}

// Cache the checked effect, before assigning this occurrence's identities.
// A section can reuse projection work while entering fresh bindings in each
// declaration. Observation metadata is never part of the cached aliases.
function checkedOpening(t,scope,node,{complete=true,effects=selectionEffects.all,receiverScope=scope,
  receiver=t.term(node,receiverScope,null)}={}) {
  const record=recordOf(t,receiverScope,receiver);
  if(!record)return null;
  scope=scope.modelEvidence(receiver);
  const spelling=sourceName(node);
  const at={start:node.start,end:node.end};
  // All projections share this activation's checked receiver. Reading one
  // selected field must not elaborate the source receiver again.
  const value={kind:"instantiated",value:receiver,args:[],...at};
  const notations=modelNotations(record),notationFields=new Set(notations.values());
  const values=new Map([...record.fields,...record.derived??[]].filter(field=>effects.labels||effects.notation&&notationFields.has(field)).map(field=>{
    const key=t.identityAdapter.key(field.projectionId);
    const unavailable=key&&receiverScope.env.get(key);
    // A refused optional operation is still a refused dependency when named;
    // opening the model must not eagerly call it and hide the checked fields.
    return [field,unavailable?.tag==="Untranslated"?unavailable
      :t.term(receiverScope.declared({kind:"call",fn:projectionReference(t,field,at),args:[value],...at}),receiverScope,null)];
  }));
  // All of them in scope with one copy of the names there.
  const added=effects.labels?[...values].map(([field,value])=>[field.name,value]):[];
  if(effects.notation)for(const [operator,field] of notations)added.push([operatorBinding(operator),values.get(field)]);
  // An ambiguous name or operator is refused where it is used.
  if(effects.labels)for(const field of Object.keys(record.ambiguous??{}))
    added.push([field,{tag:"Ambiguous",message:ambiguousField(record,spelling??"m",field).message}]);
  if(effects.notation)for(const [operator,list] of Object.entries(record.ambiguousNotations??{}))
    added.push([operatorBinding(operator),{tag:"Ambiguous",message:`${operator} is ambiguous in ${record.name}: it is ${
      list.map(e=>`${e.label}'s ${e.parentField}`).join(" and ")}. Write ${list.map(e=>notationAlternative(spelling??"m",operator,e)).join(" or ")}.`}]);
  // A theory's numeral rule, its derived operation marked notation numeral,
  // whose natural number is built from that operation's own Nat. A refused
  // operation keeps the rule, which reads the operation alone: a numeral
  // reports that failed dependency.
  const operation=values.get(notations.get("numeral"));
  const numeral=!operation?null:{model:true,natural:operation.tag==="Untranslated"?null
    :receiverScope.nf(receiverScope.infer(operation).type).domain};
  // The model's notation is the selection (L2.10a), complete: an operator
  // it does not bind is an error, except in a module of a revision before
  // L2.10j, whose sections read one by name (sectionScope).
  if(effects.notation)added.push([SELECTION,{name:spelling??"this model",recipes:modelOperandRecipes(t,receiverScope,receiver,record),complete,numeral,literal:null,
    operators:new Set([...notations.keys(),...Object.keys(record.ambiguousNotations??{})])}]);
  return {scope,added,record,receiver,effects};
}

function openingScope(t,{scope,added,record,receiver,effects},node,activation=null) {
  const spelling=sourceName(node);
  let inner=scope.aliases(added);
  // Historical name-based sections deliberately have an incomplete selection.
  // Optional observation cannot impose retained syntax's stronger contract on
  // their checking, or advertise a context with different query semantics.
  if(!activation&&scope.unit.scopePoints&&effects.notation&&!inner.env.get(SELECTION)?.complete)
    return inner.withUnit(inner.unit.with({scopeUnavailable:"Historical name-based notation has no retained contextual selection."}));
  activation??=scope.unit.scopePoints?.activation(node,scope)??null;
  if(activation) {
    const members=new Map(effects.labels?[...record.fields,...record.derived??[]].map(field=>{
      if(!field.projectionId)throw new TypeError("A retained opening needs an exact projection identity.");
      return [field.name,projectedResolution(field.projectionId,activation.bindingId)];
    }):[]);
    if(effects.labels)for(const field of Object.keys(record.ambiguous??{}))
      members.set(field,failedResolution(ambiguousField(record,spelling??"m",field)));
    inner=inner.alias(t.identityAdapter.key(activation.bindingId),receiver)
      .withSlotOutcomes(inner.slotOutcomes.activate(activation.bindingId,members));
    if(effects.notation)inner=bindNotationContext(inner,t.identityAdapter.key(activation.bindingId));
  }
  return scope.unit.scopePoints?.selected(inner,activation,effects)??inner;
}

export function notationDeclaration(t,module,d,env,declared=new Set()) {
  if(!d.retainedNotation) {
    const entry=retainSourceNotation(t,module,d,env,{declared});
    for(const [key,value] of entry.env)env.set(key,value);
    d=entry.declaration;
  }
  if(d.uses?.length||d.name.text!==d.retainedNotation.binding.label)
    throw new TypeError("A retained notation entry needs its activated source artifact.");
  const notation=retainedNotationReceipt(t,d.retainedNotation,new Scope(module,new Map(),env));
  env.set(notationBinding(d.name.text),notation);
  // By its qualified name too, which an import's notation of its name
  // leaves in place (qualified-names.mjs).
  env.set(notationBinding(`${t.moduleName}::${d.name.text}`),notation);
  env.set(t.identityAdapter.key(notation.bindingId),notation);
  registerRetainedNotationPrinting(t,d.retainedNotation,env);
}

// The scope with a named notation selected: its rules for its operators.
function notationSelected(scope,notation) {
  let inner=scope;
  const operators=[...notation.rules.keys()].filter(key=>!["numeral","literal"].includes(key));
  for(const operator of operators)inner=inner.alias(operatorBinding(operator),{tag:"NotationRule",rule:notation.rules.get(operator)});
  return inner.alias(SELECTION,{name:notation.name,identity:notation.bindingId??null,complete:true,operators:new Set(operators),
    recipes:Object.fromEntries(operators.map(key=>[key,notation.rules.get(key).recipe])),
    numeral:notation.rules.get("numeral")??null,literal:notation.rules.get("literal")??null});
}

function retainedReceiverNotation(t,scope,node) {
  const reference=node.notation.kind==="bindingReference"
    ?lowerBindingReference(node.notation,scope.unit.bindingAdapter,scope.slotOutcomes):node.notation;
  const notation=scope.env.get(referenceKey(reference));
  if(notation?.tag!=="Notation"||!notation.bindingId
    ||referenceKey(reference)!==t.identityAdapter.key(notation.bindingId))
    throw new TypeError("A retained named selection needs its exact source notation receipt.");
  if(node.model?(!notation.modelBinding||referenceKey(node.model)!==t.identityAdapter.key(notation.modelBinding))
    :notation.modelBinding)throw new TypeError("Retained attached rules need their exact source model identity.");
  return notation;
}

function invalidModelSelection(t,scope,site,receiver) {
  return scope.unit.locate(Error(`use selects a model of a theory, such as m : Group(U0); this is a value of type ${
    t.shown(scope.infer(receiver).type)}.`),site);
}

// The scope with the model `node` selected, by use m; or m.(e) (L2.4c):
// opened, or the error that it is no model.
// The name of what a list of file-level uses selects last, or null: the
// notation the declaration after them prints in (L2.10j).
export const selectionName=uses=>{const model=uses?.at(-1);return model?.kind==="name"?model.name:null;};
export function selected(t,scope,node,{effects=selectionEffects.all,activation=null}={}) {
  const site=node;
  activation??=scope.unit.scopePoints?.activation(node,scope)??null;
  if(!effects.labels&&!effects.notation)return activation
    ?scope.withSlotOutcomes(scope.slotOutcomes.activate(activation.bindingId,[])):scope;
  // Synthesized operand selection owns only its receiver environment. Apply
  // the resulting effects in the caller, preserving its names and reference
  // observations even when the receiver is a captured named notation.
  const entered=t.expressionScope(node,scope,{receiver:true});
  const receiverScope=entered.scope;node=entered.node;
  if(node.kind==="notationReceiver") {
    const notation=retainedReceiverNotation(t,receiverScope,node);
    if(node.model) {
      const receiver=t.term(node.model,receiverScope,null);
      let inner=opened(t,scope,node.model,{effects,receiver,receiverScope,activation});
      if(!inner)throw invalidModelSelection(t,scope,site,receiver);
      if(effects.notation) {
        const selection=inner.env.get(SELECTION);
        inner=inner.alias(SELECTION,{...selection,extension:notation.bindingId,
          numeral:notation.rules.get("numeral")??selection.numeral??null,
          literal:notation.rules.get("literal")??selection.literal??null});
        if(activation)inner=bindNotationContext(inner,t.identityAdapter.key(activation.bindingId));
      }
      return inner;
    }
    let inner=effects.notation?notationSelected(scope,notation):scope;
    if(activation) {
      inner=inner.withSlotOutcomes(inner.slotOutcomes.activate(activation.bindingId,[]));
      if(effects.notation)inner=bindNotationContext(inner,t.identityAdapter.key(activation.bindingId));
    }
    return scope.unit.scopePoints?.selected(inner,activation,effects)??inner;
  }
  const selector=node.kind==="bindingReference"?receiverScope.unit.bindingAdapter.resolve(node.resolution,receiverScope.slotOutcomes):null;
  if(selector?.tag==="namespace-selector") {
    if(!activation)throw new TypeError("A retained namespace selection needs its activation identity.");
    // The body occurrences hold exact interface candidates. This decision
    // carries no unused member table; each use applies its own substitution
    // after the branch selects the namespace.
    return scope.withSlotOutcomes(effects.labels?scope.slotOutcomes.selectNamespace(activation.bindingId)
      :scope.slotOutcomes.activate(activation.bindingId,[]));
  }
  const key=referenceKey(node),notation=key?receiverScope.env.get(notationBinding(key)):null;
  if(notation?.tag==="Notation"&&!notation.model) {
    const inner=effects.notation?notationSelected(scope,notation):scope;
    if(!activation)return inner;
    let activated=inner.withSlotOutcomes(inner.slotOutcomes.activate(activation.bindingId,[]));
    if(effects.notation)activated=bindNotationContext(activated,t.identityAdapter.key(activation.bindingId));
    return scope.unit.scopePoints?.selected(activated,activation,effects)??activated;
  }
  const receiver=t.term(node,receiverScope,null),inner=opened(t,scope,node,{effects,receiver,receiverScope,activation});
  // A model's notation with the literal rules its module added, where the
  // name is still that model.
  if(effects.notation&&inner&&notation?.model&&receiverScope.env.get(key)===notation.model) {
    const selection=inner.env.get(SELECTION);
    const extended=inner.alias(SELECTION,{...selection,extension:notation.bindingId??null,
      numeral:notation.rules.get("numeral")??selection.numeral??null,
      literal:notation.rules.get("literal")??selection.literal??null});
    return activation?bindNotationContext(extended,t.identityAdapter.key(activation.bindingId)):extended;
  }
  if(inner)return inner;
  throw invalidModelSelection(t,scope,site,receiver);
}

// m.(+), a model's operation that its theory's notation binds + to: the
// node of the field m.f, or the error that says why there is none.
export function qualifiedOperator(t,scope,n) {
  const at={start:n.operatorStart,end:n.operatorEnd};
  const spelling=sourceName(n.model)??"this value";
  // A named notation's operator: its rule, applied where it stands. A
  // model's notation, with the literal rules its module added, binds its
  // theory's operators, read from the model below.
  const {node:model,scope:receiverScope}=t.expressionScope(n.model,scope,{receiver:true});
  n={...n,model};
  const key=referenceKey(n.model),notation=n.model.kind==="notationReceiver"?retainedReceiverNotation(t,receiverScope,n.model)
    :key?receiverScope.env.get(notationBinding(key)):null;
  if(notation?.tag==="Notation"&&!notation.model) {
    const rule=notation.rules.get(n.operator);
    if(!rule)throw scope.unit.locate(Error(`${notation.name} binds no rule to ${n.operator}.`),at);
    return {kind:"notationRule",rule,start:n.start,end:n.end};
  }
  if(n.model.kind==="notationReceiver")n={...n,model:n.model.model};
  const record=recordOf(t,receiverScope,t.term(n.model,receiverScope,null));
  if(!record)throw scope.unit.locate(Error(`${spelling}.(${n.operator}) takes a model of a theory; ${spelling} is not one.`),n.model);
  const field=modelNotations(record).get(n.operator);
  if(!field) {
    const list=record.ambiguousNotations?.[n.operator];
    throw scope.unit.locate(Error(list
      ?`${n.operator} is ambiguous in ${record.name}: it is ${list.map(e=>`${e.label}'s ${e.parentField}`).join(" and ")}. Write ${list.map(e=>notationAlternative(spelling,n.operator,e,{applied:false})).join(" or ")}.`
      :`${record.name} binds no operation to ${n.operator}.`),at);
  }
  const operation=receiverScope.declared({kind:"call",fn:projectionReference(t,field,at),args:[n.model],start:n.start,end:n.end});
  return receiverScope===scope?operation:{kind:"scoped",node:operation,scope:receiverScope,start:n.start,end:n.end};
}

// The declarations a theory expands to, checked in its place; its record
// is in scope by its name, so that a later theory extends it. A theory that
// does not expand fails as a declaration of its name.
export function theoryDeclarations(t,sourceUnit,d,env,declarations) {
  const module=sourceUnit.declaration(t.declarationFuel).with({references:null});
  try {
    const lookup=name=>{
      const binding=env.get(name),at=d.parents.find(parent=>parent.name.text===name)?.name??d.name;
      if(binding?.tag==="Untranslated")
        throw module.locate(Object.assign(Error(`Untranslated dependency: ${name}`),
          {blockedBy:binding.blockedBy??binding.binding,cause:binding.cause??binding.reason}),at);
      // A qualified parent available nowhere (qualified-names.mjs).
      if(binding?.tag==="QualifiedFailure")throw module.locate(Error(binding.message),at);
      return env.get(theoryBinding(name))?.record??null;
    };
    const built=retainedTheoryDeclarations(t,module,d,env,{lookup,isTheory:name=>env.has(theoryBinding(name))});
    const theory={tag:"Theory",name:d.name.text,record:built.record};
    env.set(theoryBinding(d.name.text),theory);
    // By its qualified name too, which an import's theory of its name
    // leaves in place (qualified-names.mjs).
    env.set(theoryBinding(`${t.moduleName}::${d.name.text}`),theory);
    return built.declarations;
  } catch(failure) {
    propagateElaborationStop(failure);
    return failedExpansion(t,d,env,declarations,module.locate(failure,d.name));
  } finally {module.fuel.close();}
}

// `scope` with a declaration's file-level uses selected (L2.10j), in order.
export const usesScope=(t,scope,uses,{effects=selectionEffects.all}={})=>!effects.labels&&!effects.notation?scope
  :(uses??[]).reduce((inner,model)=>selected(t,inner,model,{effects}),scope);
export const sourceItemScope=(t,scope,item)=>usesScope(t,scope,item.uses,{effects:fileSelectionEffects(item.kind)});

// A declaration that does not expand, a theory or an initial or free model,
// fails as a declaration of its name, with the located `error`; it expands
// to nothing.
export function failedExpansion(t,d,env,declarations,error) {
  t.onDeclarationStart?.(d);
  declarations.push({name:d.name.text,syntax:d,status:"not-translated",...sourceFailure(error)});
  const binding=t.bindingName(d.name.text);
  t.publishDeclaration(env,d.name.text,untranslated(d.name.text,binding,error.message,failureRoot(error,binding)));
  t.onDeclaration?.(d,declarations.at(-1));
  return [];
}

// A theory's sorts need their evidence's definitions, from hlevels.
export function missingEvidence(d,env) {
  const missing=(d.requires??[]).filter(name=>!env.has(name));
  return missing.length?Error(`The sorts of ${d.generated.theory} need ${missing.join(" and ")}, from hlevels: import hlevels;`):null;
}

// T.Hom or T.Iso, or one of their operations, for a theory T whose models
// have no homomorphisms: the error that says why, or null.
export function missingMorphisms(scope,name,spelling=name) {
  const [,theory,kind]=/^(.+?)\.(Hom|Iso)(?:\.|$)/.exec(name)??[],entry=theory&&scope.env.get(theoryBinding(theory));
  // Retained artifacts publish their record with the exact checked model
  // declaration. They do not require a second nominal generator registry.
  const value=theory&&scope.env.get(theory),record=entry?.record
    ??(value?.tag==="DefRef"?scope.checker.theories?.get(value.name):null);
  const written=spelling.split(/\.(?:Hom|Iso)(?:\.|$)/)[0];
  if(record?.noMorphisms)return Error(`${written}'s models have no homomorphisms: ${record.noMorphisms}.`);
  return kind==="Iso"&&record?.noIsomorphisms
    ?Error(`${written}'s models have homomorphisms but no isomorphisms: ${record.noIsomorphisms}.`):null;
}

// A section's scope, inside its parameters (L2.4): each earlier definition of
// the section applied to the section's parameters, as the section writes
// it, and each parameter that is a model opened.
//
// Each definition of a section takes the same parameters, so its earlier
// definitions, applied, are the same terms but for the parameters' names,
// fresh for each definition: each is elaborated once for the section, and
// for a later definition its parameters renamed, where the definition and
// the parameters' types are the ones it was elaborated with. Each later
// definition elaborated them all again, a quadratic time: half of
// rationals' (sectionApplications).
const sectionApplications=new WeakMap(),OPENED=Symbol("opened");
export function sectionScope(t,scope,n) {
  const at={start:n.start,end:n.end},name=text=>({kind:"name",name:text,...at});
  const implicit=n.section.params.filter(p=>p.implicit),explicit=n.section.params.filter(p=>!p.implicit);
  const kept=sectionApplications.get(n.section.params)??sectionApplications.set(n.section.params,new Map()).get(n.section.params);
  // Each parameter's own name here, a variable's or a universe's, and the
  // parameters' types with those names as positions.
  const own=n.section.params.map(p=>{const bound=scope.env.get(p.name.text);
    return bound?.tag==="Var"?bound.name:bound?.tag==="U"&&bound.level?.tag==="Var"?bound.level.name:null;});
  const position=new Map(own.map((x,k)=>[x,`\u0000parameter${k}`]));
  const parameters=own.includes(null)?null
    :alphaKey([n.section.params.map(p=>scope.env.get(p.name.text)?.tag??null),own.map(x=>scope.context.get(x)??null)],position);
  // A kept term with its parameters' names here.
  const rename=(names,term)=>names.reduce((renamed,x,k)=>x===own[k]?renamed:substituteTerm(renamed,x,scope.env.get(n.section.params[k].name.text)),term);
  const applied=[];
  for(const declared of n.section.declared) {
    const entry=scope.env.get(declared);
    if(!entry||entry.tag==="Untranslated")continue;
    let application=kept.get(declared),term;
    if(parameters!==null&&application?.translator===t&&application.entry===entry&&application.parameters===parameters)
      term=rename(application.own,application.term);
    else {
      term=t.term({kind:"call",fn:name(declared),args:explicit.map(p=>name(p.name.text)),
        ...(implicit.length?{implicitArgs:implicit.map(p=>name(p.name.text))}:{}),...at},scope,null);
      if(parameters!==null)kept.set(declared,{translator:t,entry,parameters,own,term});
    }
    const original=scope.unit.scopePoints?.compilation.ofValue(entry,scope.unit);
    const binding=original?scope.unit.scopePoints.bind({text:declared,start:n.start,end:n.end,origin:original.origin},scope):null;
    applied.push({declared,term,binding});
  }
  let inner=scope.aliases(applied.map(({declared,term})=>[declared,term]));
  for(const {declared,term,binding} of applied)if(binding)inner=inner.sourceBinding(declared,term,binding);
  // Cache checked projections and evidence, then assign the implicit opening
  // a fresh activation in this declaration. Reusing a past scope would retain
  // its binder identities, while rechecking would change prefix work.
  const opening=kept.get(OPENED);
  if(parameters!==null&&opening?.translator===t&&opening.parameters===parameters) {
    for(const checked of opening.models) {
      const {record,effects,node}=checked;
      const evidence=checked.evidence.map(e=>({...e,term:rename(opening.own,e.term),type:rename(opening.own,e.type),model:rename(opening.own,e.model)}));
      inner=openingScope(t,{scope:inner.with({evidence:[...inner.evidence,...evidence]}),record,effects,
        receiver:rename(opening.own,checked.receiver),
        added:checked.added.map(([key,value])=>[key,isTerm(value)?rename(opening.own,value):value])},node);
    }
    return inner;
  }
  const models=[];
  // A section's selection is complete, as any other (L2.10j); a module of a
  // revision before then reads what its model's notation does not bind by
  // name.
  for(const p of n.section.params)if(p.type) {
    const node={...p.name,kind:"name",name:p.name.text};
    const checked=checkedOpening(t,inner,name(p.name.text),{complete:!t.nameBased});
    if(!checked)continue;
    const {scope:checkedScope,...effect}=checked;
    models.push({...effect,node,evidence:checkedScope.evidence.slice(inner.evidence.length)});
    inner=openingScope(t,checked,node);
  }
  if(parameters!==null)kept.set(OPENED,{translator:t,parameters,own,models});
  return inner;
}
