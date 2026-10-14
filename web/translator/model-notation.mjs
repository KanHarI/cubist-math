import {T} from "./core.mjs";
import {bindingResolution} from "../cubist/bindings.mjs";
import {bindingSyntaxView,substituteBindingSyntax} from "../cubist/binding-syntax.mjs";
import {selectionEffects} from "../cubist/scopes.mjs";
import {bindingSyntaxAdapter} from "./binding-module.mjs";

export const notationAlternative=(model,operator,entry,{applied=true}={})=>entry.call
  ?`${model}.${entry.label}.${entry.parentField}(${operator==="unary -"?"x":"x, y"})`
  :applied?`x ${model}.${entry.label}.(${operator}) y`:`${model}.${entry.label}.(${operator})`;

// Retained records select operations by identity. The nominal record format
// remains an explicit producer boundary until the production switch.
export function modelNotations(record) {
  const fields=[...record.fields,...record.derived??[]];
  return new Map(Object.entries(record.notationBindings??record.notations??{}).map(([operator,value])=>{
    const field=record.notationBindings?fields.find(field=>field.id===value.field):fields.find(field=>field.name===value);
    if(!field)throw new TypeError("A model notation must name a field in its explicit interface.");
    return [operator,field];
  }));
}

export function modelOperandRecipes(t,scope,receiver,record) {
  if(!record.notationBindings)return record.recipes??{};
  const recipes=Object.entries(record.notationBindings);
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
  let model;
  if(typeof recipe==="string")model={kind:"name",name:recipe,start:node.start,end:node.end};
  else if(recipe.kind==="retainedOperandRecipe")model={kind:"scoped",node:recipe.syntax.tree,
    scope:scope.withUnit(scope.unit.with({bindingAdapter:bindingSyntaxAdapter(recipe.syntax,t.compilationBindings.table)}))};
  else throw new TypeError("Unknown operand recipe representation.");
  return {kind:"select",effects:selectionEffects.notation,model,body:node,start:node.start,end:node.end};
}
