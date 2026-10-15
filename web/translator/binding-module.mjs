// The explicit ordinary-module migration entry. Parsing, ordered source
// resolution and elaboration remain separate; neither admission nor replay
// may reconstruct a retained declaration's references from destination names.
import {reservedReferences} from "../cubist/parser.mjs";
import {BindingAdapter,LexicalContext,bindingResolution,reservedResolution,sourceOrigin} from "../cubist/bindings.mjs";
import {resolveBindingSyntax,lowerBindingSyntax,bindingUses,bindingSyntaxView} from "../cubist/binding-syntax.mjs";
import {recursionSite} from "./match.mjs";
import {DeclarationOwnership} from "./declarations.mjs";

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
export function sourceBindingInputs(registry,env,{reserved=[]}={}) {
  const values=new Map(),lexical=[];
  for(const [label,value] of env)if(!label.startsWith("\u0000")) {
    const binding=registry.ofValue(value);
    if(binding){values.set(binding.id,value);lexical.push([label,bindingResolution(binding.id)]);}
  }
  for(const value of env.values())if(value?.tag==="Notation") {
    registry.table.get(value.bindingId);values.set(value.bindingId,value);
  }
  return bindingInputs(registry.table,values,{reserved,lexical,notations:sourceNotationInventory(registry,env)});
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

export function resolveBindingModule(ast,text,{table,source,imports=new Map(),notations=null}) {
  if(ast.imports.length||!(ast.items??ast.declarations).every(d=>d.kind==="def"))
    throw new TypeError("The binding module entry currently accepts ordinary declarations with explicit imports only.");
  const inputs=bindingInputs(table,imports,{reserved:reservedReferences(text),notations});
  let context=inputs.context;
  const ownership=new DeclarationOwnership();
  const declarations=ast.declarations.map((declaration,index)=>{
    const owner=["module",source.module,"declaration",String(index)],label=declaration.name.text;
    const binding=table.allocate([...owner,"header"],{role:"declaration",label,
      origin:sourceOrigin({...source,start:declaration.name.start,end:declaration.name.end})});
    const conflict=ownership.reserve([declaration],declaration);
    const own=declaration.params.length?declaration.params:declaration.valueParameters??[];
    const self=recursionSite(declaration,own)?binding:null;
    const syntax=resolveBindingSyntax(declaration,{table,owner,context,constructors:inputs.constructors,source,self});
    if(!conflict)context=context.bind(label,bindingResolution(binding.id));
    return {binding,syntax};
  });
  return {...inputs,ast,declarations,context};
}

export function lowerBindingModule(prepared) {
  const declarations=prepared.declarations.map(({binding,syntax})=>{
    const tree=lowerBindingSyntax(syntax,prepared.adapter);
    return {...tree,name:{...tree.name,bindingId:binding.id}};
  });
  return {...prepared.ast,items:declarations,declarations};
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
