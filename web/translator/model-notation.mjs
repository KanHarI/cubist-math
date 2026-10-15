import {T} from "./core.mjs";
import {bindingResolution} from "../cubist/bindings.mjs";
import {bindingSyntaxView,substituteBindingSyntax} from "../cubist/binding-syntax.mjs";
import {selectionEffects} from "../cubist/scopes.mjs";
import {bindingSyntaxAdapter} from "./binding-module.mjs";
import {reference} from "../cubist/references.mjs";

export {notationAlternative} from "../cubist/theory-notation.mjs";

// A checked model determines its interface through the head of its type.
export function recordOf(t,scope,value) {
  let head=scope.infer(value).type;
  while(head&&["App","LApp"].includes(head.tag))head=head.fn;
  return head?.tag==="DefRef"?t.checker.theories?.get(head.name)??null:null;
}

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
  if(!record.notationBindings)return Object.fromEntries(Object.entries(record.operandRecipes??{}).map(([operator,sides])=>
    [operator,Object.fromEntries(Object.entries(sides).map(([side,recipe])=>[side,recipe
      ?{kind:"modelOperandRecipe",receiver,record,recipe}:null]))]));
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

// Interpret the nominal producer's closed descriptor only when its operand
// is consumed. Interface labels select members of this checked model, never
// bindings in the caller. Inherited recipes run over the parent projection,
// preserving header substitution and field renaming through any number of
// inheritance steps. This runtime value is never part of retained syntax.
export function modelOperandReceiver(t,scope,node) {
  let {receiver,record,recipe}=node;
  const at={start:node.start,end:node.end};
  const value=core=>({kind:"instantiated",value:core,args:[],...at});
  const project=field=>{
    if(!field?.projectionId)throw new TypeError("An operand receiver needs its exact interface projection identity.");
    return {kind:"call",fn:reference(t.identityAdapter.key(field.projectionId),field.projection,at),
      args:[value(receiver)],...at};
  };
  for(;;)switch(recipe.tag) {
    case "source":return recipe.receiver;
    case "missing":throw Error(`Untranslated name: ${recipe.name}`);
    case "field":return project([...record.fields,...record.derived??[]].find(field=>field.name===recipe.name));
    case "parent":return project(record.parents.find(parent=>parent.label===recipe.name));
    case "parameter": {
      let type=scope.infer(receiver).type;
      for(let k=record.params.length-1;k>=0;k--) {
        if(type?.tag!=="App")throw new TypeError("An operand receiver needs its complete checked header application.");
        if(record.params[k].name===recipe.name)return value(type.arg);
        type=type.fn;
      }
      throw new TypeError("An operand receiver must belong to its explicit header.");
    }
    case "parent-recipe": {
      receiver=t.term(project(record.parents.find(parent=>parent.label===recipe.parent)),scope,null);
      record=recordOf(t,scope,receiver);
      if(!record)throw new TypeError("An inherited operand recipe needs a checked parent model.");
      recipe=recipe.recipe;
      break;
    }
    default:throw new TypeError("Unknown source operand receiver descriptor.");
  }
}

// Only the model expression enters its retained binding environment. The
// operand is elaborated in the caller with the requested notation effect;
// the selected model cannot introduce labels over the caller's names.
export function notationOperand(t,scope,node,recipe) {
  if(!recipe)return node;
  let model;
  if(typeof recipe==="string")model={kind:"name",name:recipe,start:node.start,end:node.end};
  else if(recipe.kind==="modelOperandRecipe")model={kind:"scoped",
    node:{...recipe,kind:"modelOperandReceiver",start:node.start,end:node.end},
    scope:scope.withUnit(scope.unit.with({bindingAdapter:null,references:null}))};
  else if(recipe.kind==="retainedOperandRecipe")model={kind:"scoped",node:recipe.syntax.tree,
    scope:scope.withUnit(scope.unit.with({bindingAdapter:bindingSyntaxAdapter(recipe.syntax,t.compilationBindings.table),references:null}))
      .aliases(recipe.aliases??[])};
  else throw new TypeError("Unknown operand recipe representation.");
  // The activation occurs at this operand, even when its receiver syntax
  // comes from another document. Keep that use site on the scope boundary.
  return {kind:"select",effects:selectionEffects.notation,model:{...model,start:node.start,end:node.end},
    body:node,start:node.start,end:node.end};
}
