// Named rules retain their lexical body and lazy operand binders as one
// canonical syntax family. Checked values and environments belong only to
// the elaboration receipt, never to this source artifact.
import {sourceOrigin} from "./bindings.mjs";
import {resolveBindingSyntax} from "./binding-syntax.mjs";
import {retainOperandRecipe} from "./retained-notation.mjs";

export const lexemeBindings=["cons","nil","digit","lower","upper","period","slash","underscore","plus","minus","parsed_value","parse_answer","UNat"];

export function retainNamedNotation(declaration,options) {
  if(declaration.kind!=="notation")throw new TypeError("Named notation retention needs a source notation declaration.");
  if(declaration.uses?.length)throw new TypeError("Named notation source selections must be activated before retention.");
  const {table,owner,source,model=null}=options,name=declaration.name.text;
  const origin=sourceOrigin({...source,start:declaration.start,end:declaration.end});
  const binding=table.allocate([...owner,"notation"],{role:"notation",label:name,origin});
  const rules=declaration.rules.map((rule,index)=>{
    if(model&&!["numeral","literal"].includes(rule.kind))
      throw Object.assign(Error(`A model's notation is its theory's; ${name}'s adds only a numeral or a literal rule.`),
        {offset:rule.start,sourceEnd:rule.end});
    const key=rule.kind??(rule.unary?"unary -":rule.operator),ruleOwner=[...owner,"rules",String(index)];
    const operands=rule.kind?[rule.param]:[rule.left,...rule.right?[rule.right]:[]];
    const syntax=resolveBindingSyntax({kind:"namedNotationRule",operands,value:rule.value,
      ...(rule.type?{type:rule.type}:{}),start:rule.start,end:rule.end},{...options,owner:ruleOwner});
    const recipe=retainOperandRecipe({left:rule.leftView??null,right:rule.rightView??null},options.context,
      {...options,owner:[...ruleOwner,"recipes"],theory:name});
    const readers=(key==="literal"?lexemeBindings:key==="numeral"?["UNat"]:[]).map(label=>{
      if(options.context.lookup(label).tag==="missing")throw Object.assign(key==="literal"
        ?Error(`A literal rule reads a Lexeme: import lexemes, which defines ${label}.`)
        :Error("A numeral rule reads a unary natural number: import unat."),{offset:rule.start,sourceEnd:rule.end});
      return Object.freeze([label,resolveBindingSyntax({kind:"name",name:label,start:rule.start,end:rule.start},
        {...options,owner:[...ruleOwner,"reader",label]})]);
    });
    return Object.freeze({key,syntax,recipe,readers:Object.freeze(readers)});
  });
  return Object.freeze({binding,model:model?table.get(model.id).id:null,rules:Object.freeze(rules)});
}
