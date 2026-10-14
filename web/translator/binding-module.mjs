// The explicit ordinary-module migration entry. Parsing, ordered source
// resolution and elaboration remain separate; neither admission nor replay
// may reconstruct a retained declaration's references from destination names.
import {reservedReferences} from "../cubist/parser.mjs";
import {BindingAdapter,LexicalContext,bindingResolution,reservedResolution,sourceOrigin} from "../cubist/bindings.mjs";
import {resolveBindingSyntax,lowerBindingSyntax} from "../cubist/binding-syntax.mjs";
import {recursionSite} from "./match.mjs";
import {DeclarationOwnership} from "./declarations.mjs";

// A source context and its constructor inventory come from one explicit
// identity-to-value correspondence. The lexical projection may include
// aliases or accepted scratch bindings; it never consults a destination env.
export function bindingInputs(table,values,{reserved=[],lexical=null}={}) {
  const adapter=new BindingAdapter(table,{reserved});
  const entries=lexical??[...values].map(([id])=>[table.get(id).label,bindingResolution(id)]);
  const context=new LexicalContext([...reserved.map(label=>[label,reservedResolution(label)]),...entries]);
  const constructors=[...values].filter(([,value])=>value?.tag==="InductiveConstructor").map(([id,value])=>
    ({id,label:table.get(id).label,nullary:!value.arity&&!value.dims}));
  return {adapter,context,constructors,env:new Map([...values].map(([id,value])=>[adapter.key(id),value]))};
}

export function resolveBindingModule(ast,text,{table,source,imports=new Map()}) {
  if(ast.imports.length||!(ast.items??ast.declarations).every(d=>d.kind==="def"))
    throw new TypeError("The binding module entry currently accepts ordinary declarations with explicit imports only.");
  const inputs=bindingInputs(table,imports,{reserved:reservedReferences(text)});
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
