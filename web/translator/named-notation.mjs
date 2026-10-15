import {cloneBindingSyntax,lowerBindingSyntax,bindingUses} from "../cubist/binding-syntax.mjs";
import {sourceOrigin} from "../cubist/bindings.mjs";
import {bindingSyntaxAdapter} from "./binding-module.mjs";
import {retainNamedNotation} from "../cubist/named-notation.mjs";
import {enterSourceItem} from "./retained-source-context.mjs";
import {notationPrintingRecipe} from "./model-notation.mjs";
import {SELECTION,notationContextKey,NUMERAL_NAT,lexemeKey} from "./notation-context.mjs";

// The source producer owns model attachment and ordered file activation.
// A later destination only consumes the resulting artifact and explicit
// captures; it cannot reclassify a standalone notation by its public label.
export function retainSourceNotation(t,module,declaration,env,{declared=new Set(),
  owner=["notations",module.moduleName,String(declaration.start)]}={}) {
  const registry=t.compilationBindings,name=declaration.name.text;
  const value=env.get(name),model=value&&value.tag!=="Untranslated"?registry.ofValue(value):null;
  if(value&&value.tag!=="Untranslated") {
    if(!declared.has(name))throw module.locate(Error(`${name} is declared in another module: only the module that declares a model adds rules to its notation.`),declaration.name);
    if(!model)throw new TypeError("A source model's notation needs its declaration identity.");
  }
  const {source,inputs,prepared,captures}=enterSourceItem(t,module,declaration,env,owner);
  const artifact=retainNamedNotation(prepared.item,{table:registry.table,owner,source,
    context:prepared.context,constructors:inputs.constructors,simpSets:inputs.simpSets,model});
  return {artifact,prepared,env:captures,
    declaration:{...prepared.item,retainedNotation:artifact}};
}

// Printing metadata reads the same retained function/operand identities as
// elaboration. Labels here describe the selected notation only; they never
// resolve the function again in a later module.
export function registerRetainedNotationPrinting(t,artifact,env) {
  for(const rule of artifact.rules) {
    const adapter=bindingSyntaxAdapter(rule.syntax,t.compilationBindings.table);
    const tree=lowerBindingSyntax(rule.syntax,adapter),v=tree.value;
    if(v.kind!=="call"||v.fn.kind!=="name")continue;
    const f=env.get(v.fn.name);
    if(f?.tag!=="DefRef")continue;
    const operands=tree.operands.map(token=>adapter.key(token.bindingId));
    let entry;
    if(rule.key==="literal"&&v.args.length===1&&v.args[0].name===operands[0])entry={literal:true};
    else if(rule.key==="numeral"&&v.args.some(arg=>arg.name===operands[0])
      &&v.args.every(arg=>arg.name===operands[0]||arg.kind==="number"))
      entry={numeral:v.args.map(arg=>arg.kind==="number"?arg.value:null)};
    else if(operands.length===2&&v.args.length===2&&v.args.every((arg,i)=>arg.name===operands[i]))
      entry={operator:rule.key,recipe:notationPrintingRecipe(rule.recipe)};
    if(entry) {
      const printing=t.checker.notationPrinting??=new Map();
      printing.set(f.name,[...(printing.get(f.name)??[]),{notation:artifact.binding.label,...entry}]);
    }
  }
}

// Capture a rule's source values once. Only this ephemeral receipt contains
// checked values; the portable artifact holds syntax and IDs alone. An
// unresolved source occurrence remains unresolved even if the caller happens
// to provide the same public label.
export function retainedNotationReceipt(t,artifact,scope) {
  const table=t.compilationBindings.table;
  if(table.get(artifact.binding.id).role!=="notation")throw new TypeError("Named rules need a notation identity.");
  const model=artifact.model?scope.env.get(t.identityAdapter.key(artifact.model)):null;
  if(artifact.model&&(!model||model.tag==="Untranslated"))
    throw new TypeError("Retained attached rules need their exact source model receipt.");
  const captures=syntax=>{
    const aliases=new Map();
    for(const use of bindingUses(syntax,{conditional:true}))if(use.id) {
      const key=t.identityAdapter.key(use.id),context=notationContextKey(key);
      if(scope.env.has(key))aliases.set(key,scope.env.get(key));
      if(scope.env.has(context))aliases.set(context,scope.env.get(context));
    }
    return aliases;
  };
  const rules=new Map();
  for(const rule of artifact.rules) {
    const aliases=captures(rule.syntax);
    for(const [label,syntax] of rule.readers) {
      const adapter=bindingSyntaxAdapter(syntax,table),node=lowerBindingSyntax(syntax,adapter,scope.slotOutcomes);
      const value=node.kind==="name"&&scope.env.has(node.name)?scope.env.get(node.name)
        :t.term(node,scope.withUnit(scope.unit.with({bindingAdapter:adapter,references:null})),null);
      aliases.set(rule.key==="literal"?lexemeKey(label):NUMERAL_NAT,value);
    }
    const recipe=Object.fromEntries(Object.entries(rule.recipe).map(([side,syntax])=>[side,syntax
      ?{kind:"retainedOperandRecipe",syntax,aliases:[...captures(syntax)]}:null]));
    rules.set(rule.key,{binding:artifact.binding.id,syntax:rule.syntax,recipe,aliases,
      ...(rule.key==="numeral"?{natural:NUMERAL_NAT}:{})});
  }
  return Object.freeze({tag:"Notation",bindingId:artifact.binding.id,name:artifact.binding.label,rules,model,
    modelBinding:artifact.model});
}

// Both rule application and an operator section enter the source rule's
// environment. Foreign implementation offsets belong to the caller's site;
// lazy operands still enter their own caller scopes.
function ruleScope(scope,rule,adapter,site) {
  const blameSite=scope.unit.blameSite??(rule.syntax.tree.origin.module!==scope.unit.moduleName
    ?{start:site.start,end:site.end}:null);
  return scope.withUnit(scope.unit.with({bindingAdapter:adapter,references:null,blameSite,
    scopeUnavailable:"Notation expansion awaits its contextual observation migration."}));
}

// Each invocation owns fresh local/activation/pattern identities. Arguments
// remain suspended in their caller scope and are elaborated only where the
// rule consumes them, preserving macro laziness and caller name resolution.
export function appliedRetainedRule(t,scope,rule,left,right,site=left) {
  const source=site.origin??sourceOrigin({revision:t.compilationBindings.revision,module:scope.unit.moduleName,
    start:site.start,end:site.end});
  const {syntax}=cloneBindingSyntax(rule.syntax,t.compilationBindings.table,["notation-expansions",rule.binding],
    {expansion:{kind:"notation",site:source,binding:rule.binding}});
  const adapter=bindingSyntaxAdapter(syntax,t.compilationBindings.table);
  let inner=ruleScope(scope,rule,adapter,site).alias(SELECTION,null).aliases(rule.aliases??[]);
  for(const [index,operand] of syntax.tree.operands.entries()) {
    const node=[left,right][index];
    if(!node)throw new TypeError("A named notation rule needs every explicit operand argument.");
    inner=inner.alias(adapter.key(operand.bindingId),{tag:"SourceOperand",node,scope});
  }
  return {node:lowerBindingSyntax(syntax,adapter,inner.slotOutcomes).value,scope:inner};
}

export function retainedRuleOperation(t,scope,rule,site) {
  const adapter=bindingSyntaxAdapter(rule.syntax,t.compilationBindings.table);
  const tree=lowerBindingSyntax(rule.syntax,adapter),value=tree.value;
  const operands=tree.operands.map(token=>adapter.key(token.bindingId));
  if(value.kind!=="call"||operands.length!==2||value.args.length!==2
    ||!value.args.every((arg,index)=>arg.kind==="name"&&arg.name===operands[index]))return null;
  // Source syntax allowed a name here, including a qualified model member.
  // Resolution may have made that name structural; it stays an exact source
  // reference instead of being classified again from a destination label.
  if(!["bindingReference","member"].includes(rule.syntax.tree.value.fn.kind))return null;
  return {node:value.fn,scope:ruleScope(scope,rule,adapter,site).aliases(rule.aliases)};
}
