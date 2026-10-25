// Binding inputs and the single retained-declaration elaboration boundary.
import {reservedReferences} from "../cubist/parser.mjs";
import {BindingAdapter,LexicalContext,bindingResolution,reservedResolution,failedResolution} from "../cubist/bindings.mjs";
import {lowerBindingSyntax,bindingUses,bindingSyntaxView} from "../cubist/binding-syntax.mjs";

// A source context and its constructor inventory come from one explicit
// identity-to-value correspondence. The lexical projection may include
// aliases or accepted scratch bindings; it never consults a destination env.
export function bindingInputs(table,values,{reserved=[],lexical=null,notations=null}={}) {
  const adapter=new BindingAdapter(table,{reserved});
  const entries=lexical??[...values].map(([id])=>[table.get(id).label,bindingResolution(id)]);
  let context=new LexicalContext([...reserved.map(label=>[label,reservedResolution(label)]),...entries]);
  if(notations!==null)context=context.withNotations(notations);
  const constructors=[...values].filter(([,value])=>value?.tag==="InductiveConstructor").map(([id,value])=>
    ({id,label:table.get(id).label,nullary:!value.arity&&!value.dims}));
  return {adapter,context,constructors,env:new Map([...values].map(([id,value])=>[adapter.key(id),value]))};
}

// Source entry has the complete ordered environment, including its separate
// notation namespace. A term-only identity map cannot establish the absence
// of a named notation. Later lexical binders preserve this inventory while
// the selector checks whether a model extension still names that model.
export function sourceBindingInputs(registry,env,{reserved=[],simpRegistry=null}={}) {
  const values=new Map(),lexical=[];
  for(const [label,value] of env)if(!label.startsWith("\u0000")) {
    // A qualified name available nowhere keeps its refusal (qualified-names.mjs).
    if(value?.tag==="QualifiedFailure"){lexical.push([label,failedResolution({message:value.message})]);continue;}
    const binding=registry.ofValue(value);
    if(binding){values.set(binding.id,value);lexical.push([label,bindingResolution(binding.id)]);}
  }
  for(const value of env.values())if(value?.tag==="Notation") {
    registry.table.get(value.bindingId);values.set(value.bindingId,value);
  }
  const {sets:simpSets,captures}=sourceSimpSets(registry.table,simpRegistry);
  for(const [id,value] of captures)values.set(id,value);
  return {...bindingInputs(registry.table,values,{reserved,lexical,notations:sourceNotationInventory(registry,env)}),simpSets};
}

// Source producers and isolated queries consume the same checked registry.
// Its portable inventory contains IDs only; captures remain explicit values
// in the current kernel and never become serialized syntax or lexical data.
export function sourceSimpSets(table,registry) {
  const captures=new Map();
  const sets=registry?new Map([...registry.sets].map(([label,set])=>[label,set.ambiguous
    ?{failure:failedResolution(Error(`Simplification set ${label} is ambiguous: ${set.origins.join(", ")}.`))}
    :{rules:set.rules.map(rule=>{
      table.get(rule.binding);captures.set(rule.binding,rule.term);
      return {id:rule.binding,label:rule.sourceName};
    })}])):null;
  return {sets,captures};
}

// Module entry and replayed local scopes describe the same selection
// namespace. Attached rules retain their declaring model even when a local
// binding currently shadows that model's public label.
export function sourceNotationInventory(registry,env) {
  return [...env].filter(([label,value])=>label.startsWith("\u0000notation ")&&value?.tag==="Notation")
    .map(([label,value])=>{
      const model=value.model?registry.ofValue(value.model):null;
      if(value.model&&!model)throw new TypeError("A model's notation needs its declaration identity.");
      return {name:label.slice("\u0000notation ".length),model:model?bindingResolution(model.id):null,
        notation:bindingResolution(value.bindingId)};
    });
}

// A retained declaration is inert syntax plus ownership metadata. It may
// share a queue with ordinary source declarations; no adapter or live value
// is serialized with it. Generators keep their canonical interfaces and
// hand this final declaration to the normal admission/publication path.
export function bindingDeclaration(binding,syntax,annotations={}) {
  if(binding.role!=="declaration"||!["def","inductive"].includes(syntax.tree.kind))
    throw new TypeError("A retained declaration needs a declaration identity and complete declaration syntax.");
  const {tree,...bindings}=bindingSyntaxView(syntax,syntax.tree,{inferred:syntax.inferred});
  return {...annotations,...tree,name:{...tree.name,text:binding.label,bindingId:binding.id},bindings};
}

// Only the declaration now entering elaboration is lowered. The surrounding
// source keeps its own migration boundary. Reserved references are validated
// against the language namespace, including universes carried from imports.
export function lowerBindingDeclaration(declaration,table) {
  const {bindings,theory,generated,...tree}=declaration;
  if(!["def","inductive"].includes(tree.kind)||!tree.name.bindingId)
    throw new TypeError("Invalid retained declaration entry.");
  table.get(tree.name.bindingId);
  const syntax={...bindings,tree};
  const adapter=bindingSyntaxAdapter(syntax,table);
  return {adapter,declaration:{...lowerBindingSyntax(syntax,adapter),
    ...(theory?{theory}:{}),...(generated?{generated}:{})}};
}

export function bindingSyntaxAdapter(syntax,table) {
  const reserved=bindingUses(syntax,{conditional:true}).filter(use=>use.kind==="reserved").map(use=>use.label);
  const allowed=new Set(reservedReferences(reserved.join(" ")));
  for(const label of reserved)if(!allowed.has(label))throw new TypeError(`A late lookup is not allowed: ${label}`);
  return new BindingAdapter(table,{reserved});
}
