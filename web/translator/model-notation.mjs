import {T} from "./core.mjs";
import {bindingResolution} from "../cubist/bindings.mjs";
import {bindingSyntaxView,substituteBindingSyntax} from "../cubist/binding-syntax.mjs";
import {selectionEffects} from "../cubist/scopes.mjs";
import {bindingSyntaxAdapter} from "./binding-module.mjs";

export {notationAlternative} from "../cubist/theory-notation.mjs";

// Printing describes the views captured by the retained rule, without
// resolving those names in the destination.
export const notationPrintingRecipe=recipe=>Object.fromEntries(Object.entries(recipe)
  .map(([side,syntax])=>[side,syntax?.tree.spelling??null]));
// The identity of the named notation each view captured, which reads an
// operand's numerals as the printer prints them bare; null for a view that
// selects a model.
export const notationPrintingViews=recipe=>Object.fromEntries(Object.entries(recipe)
  .map(([side,syntax])=>[side,syntax?.tree.resolution?.tag==="notation"?syntax.tree.resolution.id:null]));

// A checked model determines its interface through the head of its type.
export function recordOf(t,scope,value) {
  let head=scope.infer(value).type;
  while(head&&["App","LApp"].includes(head.tag))head=head.fn;
  return head?.tag==="DefRef"?t.checker.theories?.get(head.name)??null:null;
}

// A model selects an operation by its retained field identity.
export function modelNotations(record) {
  const fields=[...record.fields,...record.derived??[]];
  return new Map(Object.entries(record.notationBindings??{}).map(([operator,value])=>{
    const field=fields.find(field=>field.id===value.field);
    if(!field)throw new TypeError("A model notation must name a field in its explicit interface.");
    return [operator,field];
  }));
}

export function modelOperandRecipes(t,scope,receiver,record) {
  const recipes=Object.entries(record.notationBindings??{});
  if(!recipes.some(([,rule])=>rule.recipe.left||rule.recipe.right))return {};
  const table=t.compilationBindings.table,parameters=record.bindingSyntax.tree.params,arguments_=new Map();
  let type=scope.infer(receiver).type;
  for(let k=parameters.length-1;k>=0;k--) {
    const parameter=parameters[k];
    if(type?.tag!==(parameter.bound?"LApp":"App"))
      throw new TypeError("A model notation needs its complete checked header application.");
    arguments_.set(parameter.name.bindingId,parameter.bound?T.universe(type.level):type.arg);
    type=type.fn;
  }
  const instantiate=syntax=>{
    if(!syntax)return null;
    const origin=syntax.tree.origin,at={origin,start:origin.start,end:origin.end};
    const value=core=>({kind:"instantiated",value:core,args:[],...at});
    const replacements=new Map([...arguments_].map(([id,core])=>[id,bindingSyntaxView(syntax,value(core))]));
    for(const field of [...record.fields,...record.derived??[]]) {
      if(!field.id||!field.projectionId)throw new TypeError("A retained notation needs exact field and projection identities.");
      replacements.set(field.id,bindingSyntaxView(syntax,{kind:"call",fn:{kind:"bindingReference",
        resolution:bindingResolution(field.projectionId),spelling:field.projection,...at},args:[value(receiver)],...at}));
    }
    return {kind:"retainedOperandRecipe",syntax:substituteBindingSyntax(syntax,replacements,table,
      ["model-notation",record.modelId])};
  };
  return Object.fromEntries(recipes.map(([operator,rule])=>[operator,
    {left:instantiate(rule.recipe.left),right:instantiate(rule.recipe.right)}]));
}

// Only the model expression enters its retained binding environment. The
// operand is elaborated in the caller with the requested notation effect;
// the selected model cannot introduce labels over the caller's names.
export function notationOperand(t,scope,node,recipe) {
  if(!recipe)return node;
  if(recipe.kind!=="retainedOperandRecipe")throw new TypeError("An operand needs its source-resolved recipe.");
  const model={kind:"scoped",node:recipe.syntax.tree,
    scope:scope.withUnit(scope.unit.with({bindingAdapter:bindingSyntaxAdapter(recipe.syntax,t.compilationBindings.table),references:null}))
      .aliases(recipe.aliases??[])};
  // The activation occurs at this operand, even when its receiver syntax
  // comes from another document. Keep that use site on the scope boundary.
  return {kind:"select",effects:selectionEffects.notation,model:{...model,start:node.start,end:node.end},
    body:node,start:node.start,end:node.end};
}
