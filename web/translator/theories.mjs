// Theories in elaboration (L2.4, docs/roadmaps/core-theories.md): a theory
// declaration's expansion (web/cubist/theories.mjs) and the records it
// leaves, by which m.f reads a field of a model m and `open m;` puts a
// model's fields and notation in scope.
import {expandTheory} from "../cubist/theories.mjs";
import {rewritten} from "../cubist/scopes.mjs";

// The scope's key for an operator a model's notation binds: no source name
// can spell it.
export const operatorBinding = operator => "\u0000operator " + operator;
// The environment's key for a theory's record. The theory's name is its type
// of models (L2.4c), a definition like any other.
export const theoryBinding = name => "\u0000theory " + name;
// The environment's key for a named notation's rules (L2.10a), and the
// scope's key for the selected notation: its name and the operators it
// binds. A selection is complete: an operator it does not bind is an error,
// never an earlier selection's or a function named add.
export const notationBinding = name => "\u0000notation " + name;
export const SELECTION = "\u0000selection";
// The extensible operators a notation can bind, unary - as "unary -".
export const notationOperators = ["+", "-", "*", "/", "^", "<", "<=", "unary -"];

// The record of the theory whose models `value` is one of, from the head of
// its type, T(U), or null.
export function recordOf(t,scope,value) {
  let head=scope.infer(value).type;
  while(head&&["App","LApp"].includes(head.tag))head=head.fn;
  return head?.tag==="DefRef"?t.checker.theories?.get(head.name)??null:null;
}

// A theory's records, by the binding of its type of models, and its
// projections, which print as m.f.
export function registerTheoryDeclaration(t,d) {
  const binding=t.checker.bindingName?.(d.name.text)??d.name.text;
  if(d.theory)(t.checker.theories??=new Map()).set(binding,d.theory);
  if(d.generated?.role==="projection")(t.checker.theoryProjections??=new Map()).set(binding,d.generated.field);
  // A projection whose field a notation names prints with that operator
  // where its model is selected (L2.10d).
  if(d.theory)for(const [operator,field] of Object.entries(d.theory.notations??{}))
    if(!["unary -","numeral"].includes(operator))
      (t.checker.notationPrinting??=new Map()).set(t.checker.bindingName?.(`${d.theory.name}.${field}`)??`${d.theory.name}.${field}`,[{operator,model:true}]);
}

// n.name is m.f: when m is a model of a theory, the node of the call T.f(m),
// or T.p(m) for a parent labelled p; otherwise null.
export function modelField(t,scope,n) {
  const dot=n.name.lastIndexOf("."),first=dot>0?n.name.slice(0,n.name.indexOf(".")):null,root=first?scope.env.get(first):null;
  // A name under a theory's, T.Hom, is a qualified name, not a field. A
  // local model that shadows the theory's name is a model like any other.
  if(!root||theoryRoot(t,scope,first,root))return null;
  const owner={...n,name:n.name.slice(0,dot),end:n.start+dot};
  const record=recordOf(t,scope,t.term(owner,scope,null));
  if(!record)return null;
  const field=n.name.slice(dot+1);
  const known=record.fields.find(f=>f.name===field)??record.derived?.find(d=>d.name===field)??record.parents.find(p=>p.label===field);
  if(!known&&record.ambiguous?.[field])throw ambiguousField(record,owner.name,field);
  if(!known)throw Error(`${owner.name} is a model of ${record.name}, which has no field ${field}: it has ${record.fields.map(f=>f.name).join(", ")}${
    record.parents.length?`, and the parents ${record.parents.map(p=>p.label).join(", ")}`:""}.`);
  return {kind:"call",fn:{...n,name:known.projection},args:[owner],start:n.start,end:n.end};
}

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
  if(!record)throw Error(`.${field} reads a field of a model of a theory; this value is not one.`);
  const known=record.fields.find(f=>f.name===field)??record.derived?.find(d=>d.name===field)??record.parents.find(p=>p.label===field);
  if(!known&&record.ambiguous?.[field])throw ambiguousField(record,"m",field);
  if(!known)throw Error(`This is a model of ${record.name}, which has no field ${field}: it has ${record.fields.map(f=>f.name).join(", ")}${
    record.parents.length?`, and the parents ${record.parents.map(p=>p.label).join(", ")}`:""}.`);
  return {kind:"call",fn:{kind:"name",name:known.projection,start:n.field.start,end:n.field.end},args:[n.value],start:n.start,end:n.end};
}

// The scope with the model `node` opened, or null when it is no model: each
// field by its name, as its projection T.f(m), and each notation of the
// theory as m's operation. A later binding of a name or operator shadows it.
export function opened(t,scope,node,{complete=true}={}) {
  const record=recordOf(t,scope,t.term(node,scope,null));
  if(!record)return null;
  const at={start:node.start,end:node.end};
  const values=new Map([...record.fields,...record.derived??[]].map(field=>
    [field.name,t.term({kind:"call",fn:{kind:"name",name:field.projection,...at},args:[node],...at},scope,null)]));
  let inner=scope;
  for(const [name,value] of values)inner=inner.alias(name,value);
  for(const [operator,field] of Object.entries(record.notations))inner=inner.alias(operatorBinding(operator),values.get(field));
  // An ambiguous name or operator is refused where it is used.
  for(const field of Object.keys(record.ambiguous??{}))
    inner=inner.alias(field,{tag:"Ambiguous",message:ambiguousField(record,node.name??"m",field).message});
  for(const [operator,list] of Object.entries(record.ambiguousNotations??{}))
    inner=inner.alias(operatorBinding(operator),{tag:"Ambiguous",message:`${operator} is ambiguous in ${record.name}: it is ${
      list.map(e=>`${e.label}'s ${e.parentField}`).join(" and ")}. Write ${list.map(e=>`x ${node.name??"m"}.${e.label}.(${operator}) y`).join(" or ")}.`});
  // A theory's numeral rule, its derived operation marked notation numeral.
  const numeral=record.notations.numeral?{left:"n",right:null,aliases:new Map(),recipe:{},
    value:{kind:"call",fn:{kind:"name",name:operatorBinding("numeral"),...at},args:[{kind:"name",name:"n",...at}],...at}}:null;
  // The model's notation is the selection (L2.10a). A section's is not
  // complete until L2.10j: an operator it does not bind falls back by name,
  // as before views.
  return inner.alias(SELECTION,{name:node.name??"this model",recipes:record.recipes??{},complete,numeral,literal:null,
    operators:new Set([...Object.keys(record.notations),...Object.keys(record.ambiguousNotations??{})])});
}

// A named notation (L2.10a): each rule's right side, its free names read
// where the notation is declared, under keys no source name can spell, so
// that no later binding changes what a rule means. A qualified name, m.f,
// is read by its root where only the root is bound, so a later local m
// does not take its place.
// The library's names a literal's lexeme is built from (lexemes.cubist).
const LEXEME_NAMES=["cons","nil","digit","lower","upper","period","slash","underscore","plus","minus","parsed_value","parse_answer"];
// The key of a lexeme's glyph in a literal rule's scope, which no source
// name can spell. (A function, not a template: the diagnostics catalogue
// reads template-returning arrows as messages.)
export function lexemeKey(name) { return "\u0000lexeme "+name; }
export function notationDeclaration(t,module,d,env,declared=new Set()) {
  const rules=new Map();
  // A notation named after a model of this module adds literal rules to
  // that model's notation (L2.10c); no other module can.
  const model=env.has(d.name.text)&&env.get(d.name.text)?.tag!=="Untranslated";
  if(model&&!declared.has(d.name.text))
    throw module.locate(Error(`${d.name.text} is declared in another module: only the module that declares a model adds rules to its notation.`),d.name);
  for(const rule of d.rules) {
    if(model&&!["numeral","literal"].includes(rule.kind))
      throw module.locate(Error(`A model's notation is its theory's; ${d.name.text}'s adds only a numeral or a literal rule.`),rule.keyword??rule.operatorToken??d.name);
    const aliases=new Map(),pattern=new Set([rule.left?.text,rule.right?.text,rule.param?.text].filter(Boolean));
    const alias=name=>{
      const key=`\u0000notation ${d.name.text} ${name}`;
      aliases.set(key,env.get(name));
      return key;
    };
    const value=renameFree(rule.value,name=>{
      if(pattern.has(name))return null;
      if(env.has(name))return alias(name);
      const dot=name.indexOf("."),root=dot>0?name.slice(0,dot):null;
      return root&&env.has(root)?`${alias(root)}${name.slice(dot)}`:null;
    });
    // A literal rule builds its lexeme from the library's glyphs, read here.
    if(rule.kind==="literal")for(const name of LEXEME_NAMES) {
      if(!env.has(name))throw module.locate(Error(`A literal rule reads a Lexeme: import lexemes, which defines ${name}.`),rule.keyword);
      aliases.set(lexemeKey(name),env.get(name));
    }
    const key=rule.kind??(rule.unary?"unary -":rule.operator);
    rules.set(key,{left:rule.left?.text??rule.param?.text,right:rule.right?.text??null,value,aliases,source:rule.value,
      recipe:{left:rule.leftView?.text??null,right:rule.rightView?.text??null}});
  }
  env.set(notationBinding(d.name.text),{tag:"Notation",name:d.name.text,rules,model});
  // How its rules print (L2.10d): an operator whose rule applies a function
  // to its operands in order, x + y := add(x, y); a literal rule's parser,
  // literal(s) := parse(s); and a numeral rule's function of the numeral,
  // numeral(n) := int(n, 0), with its other arguments fixed numerals.
  const binding=name=>{const value=env.get(name);return value?.tag==="DefRef"?value.name:null;};
  for(const rule of d.rules) {
    const v=rule.value;
    if(v.kind!=="call"||v.fn.kind!=="name")continue;
    const f=binding(v.fn.name),printing=t.checker.notationPrinting??=new Map();
    if(!f)continue;
    // A function several notations use keeps each, the first declared
    // printing it where none of them is selected.
    const add=entry=>printing.set(f,[...(printing.get(f)??[]),entry]);
    if(rule.kind==="literal"&&v.args.length===1&&v.args[0].name===rule.param.text)
      add({notation:d.name.text,literal:true});
    else if(rule.kind==="numeral"&&v.args.some(arg=>arg.name===rule.param.text)
        &&v.args.every(arg=>arg.name===rule.param.text||arg.kind==="number"))
      add({notation:d.name.text,numeral:v.args.map(arg=>arg.kind==="number"?arg.value:null)});
    else if(!rule.kind&&!rule.unary&&v.args.length===2&&v.args[0].name===rule.left.text&&v.args[1].name===rule.right.text)
      add({notation:d.name.text,operator:rule.operator});
  }
}

// A copy of a syntax tree with each free name that `rename` maps renamed,
// whatever binds it (scopes.mjs).
const renameFree=(node,rename)=>rewritten(node,(n,bound)=>{
  if(n.kind!=="name"||bound.has(n.name.split(".")[0]))return n;
  const renamed=rename(n.name);
  return renamed?{...n,name:renamed}:n;
});

// A named notation's rule applied to two operands: its right side, and the
// scope that resolves its names. Each operand is elaborated where the rule
// uses it, in the scope the operator is written in: no binder of the rule
// captures a name of an operand.
export function appliedRule(scope,rule,left,right) {
  // The rule's own names are read in a scope with no selection, where it
  // was declared; its operands where they stand, in the use's scope.
  let inner=scope.alias(SELECTION,null);
  for(const [key,value] of rule.aliases)inner=inner.alias(key,value);
  const scoped=node=>node&&{kind:"scoped",node,scope,start:node.start,end:node.end};
  const operands=new Map([[rule.left,scoped(left)],...(rule.right?[[rule.right,scoped(right)]]:[])]);
  const substituted=substitute(rule.value,operands);
  return {node:substituted,scope:inner};
}
const substitute=(node,operands)=>rewritten(node,(n,bound)=>
  n.kind==="name"&&operands.has(n.name)&&!bound.has(n.name)?operands.get(n.name):n);

// The scope with a named notation selected: its rules for its operators.
function notationSelected(scope,notation) {
  let inner=scope;
  const operators=[...notation.rules.keys()].filter(key=>!["numeral","literal"].includes(key));
  for(const operator of operators)inner=inner.alias(operatorBinding(operator),{tag:"NotationRule",rule:notation.rules.get(operator)});
  return inner.alias(SELECTION,{name:notation.name,complete:true,operators:new Set(operators),
    recipes:Object.fromEntries(operators.map(key=>[key,notation.rules.get(key).recipe])),
    numeral:notation.rules.get("numeral")??null,literal:notation.rules.get("literal")??null});
}

// The scope with the model `node` selected, by use m; or m.(e) (L2.4c):
// opened, or the error that it is no model.
export function selected(t,scope,node) {
  const notation=node.kind==="name"?scope.env.get(notationBinding(node.name)):null;
  if(notation?.tag==="Notation"&&!notation.model)return notationSelected(scope,notation);
  const inner=opened(t,scope,node);
  // A model's notation with the literal rules its module added.
  if(inner&&notation?.model) {
    const selection=inner.env.get(SELECTION);
    return inner.alias(SELECTION,{...selection,numeral:notation.rules.get("numeral")??selection.numeral??null,
      literal:notation.rules.get("literal")??selection.literal??null});
  }
  if(inner)return inner;
  throw scope.unit.locate(Error(`use selects a model of a theory, such as m : Group(U0); this is a value of type ${
    t.shown(scope.infer(t.term(node,scope,null)).type)}.`),node);
}

// m.(+), a model's operation that its theory's notation binds + to: the
// node of the field m.f, or the error that says why there is none.
export function qualifiedOperator(t,scope,n) {
  const at={start:n.operatorStart,end:n.operatorEnd};
  // A named notation's operator: its rule, applied where it stands.
  const notation=n.model.kind==="name"?scope.env.get(notationBinding(n.model.name)):null;
  if(notation?.tag==="Notation") {
    const rule=notation.rules.get(n.operator);
    if(!rule)throw scope.unit.locate(Error(`${notation.name} binds no rule to ${n.operator}.`),at);
    return {kind:"notationRule",rule,start:n.start,end:n.end};
  }
  const record=recordOf(t,scope,t.term(n.model,scope,null));
  if(!record)throw scope.unit.locate(Error(`${n.model.name}.(${n.operator}) takes a model of a theory; ${n.model.name} is not one.`),n.model);
  const field=record.notations[n.operator];
  if(!field) {
    const list=record.ambiguousNotations?.[n.operator];
    throw scope.unit.locate(Error(list
      ?`${n.operator} is ambiguous in ${record.name}: it is ${list.map(e=>`${e.label}'s ${e.parentField}`).join(" and ")}. Write ${list.map(e=>`${n.model.name}.${e.label}.(${n.operator})`).join(" or ")}.`
      :`${record.name} binds no operation to ${n.operator}.`),at);
  }
  return {kind:"member",value:n.model,field:{text:field,...at},dot:at,start:n.start,end:n.end};
}

// The declarations a theory expands to, checked in its place; its record
// is in scope by its name, so that a later theory extends it. A theory that
// does not expand fails as a declaration of its name.
export function theoryDeclarations(t,module,d,env,declarations) {
  try {
    // A declared type whose header says it is a proposition, as Trunc's
    // : prop U does, states a law (L2.10k).
    const proposition=name=>{const entry=env.get(name);
      return entry?.tag==="Inductive"&&(entry.modifier==="prop"||entry.modifier?.trunc===-1);};
    const generated=expandTheory(d,name=>env.get(theoryBinding(name))?.record??null,proposition);
    env.set(theoryBinding(d.name.text),{tag:"Theory",name:d.name.text,record:generated[0].theory});
    return generated;
  } catch(failure) {
    // The message says where, as an elaboration error does.
    const error=module.locate(Error(failure.message),{start:failure.offset,end:failure.offset});
    t.onDeclarationStart?.(d);
    declarations.push({name:d.name.text,status:"not-translated",reason:error.message,errorStart:error.offset,errorEnd:error.sourceEnd});
    env.set(d.name.text,{tag:"Untranslated",name:d.name.text,binding:t.checker.bindingName?.(d.name.text)??d.name.text,reason:error.message});
    t.onDeclaration?.(d,declarations.at(-1));
    return [];
  }
}

// A theory's sorts need their evidence's definitions, from hlevels.
export function missingEvidence(d,env) {
  const missing=(d.requires??[]).filter(name=>!env.has(name));
  return missing.length?Error(`The sorts of ${d.generated.theory} need ${missing.join(" and ")}, from hlevels: import hlevels;`):null;
}

// T.Hom or T.Iso, or one of their operations, for a theory T whose models
// have no homomorphisms: the error that says why, or null.
export function missingMorphisms(scope,name) {
  const [,theory,kind]=/^(.+?)\.(Hom|Iso)(?:\.|$)/.exec(name)??[],entry=theory&&scope.env.get(theoryBinding(theory));
  if(entry?.record.noMorphisms)return Error(`${theory}'s models have no homomorphisms: ${entry.record.noMorphisms}.`);
  return kind==="Iso"&&entry?.record.noIsomorphisms
    ?Error(`${theory}'s models have homomorphisms but no isomorphisms: ${entry.record.noIsomorphisms}.`):null;
}

// The rest of a theory whose type of models failed, `model`: taken off the
// queue, each unavailable as a dependency of that type.
export function skipTheory(t,queue,env,model) {
  for(let k=queue.length-1;k>=0;k--) {
    const d=queue[k];
    if(d.generated?.theory!==model.generated.theory)continue;
    queue.splice(k,1);
    env.set(d.name.text,{tag:"Untranslated",name:d.name.text,binding:t.checker.bindingName?.(d.name.text)??d.name.text,
      reason:`Untranslated dependency: ${model.name.text}`});
  }
}

// A section's scope, inside its parameters (L2.4): each earlier definition of
// the section applied to the section's parameters, as the section writes
// it, and each parameter that is a model opened.
export function sectionScope(t,scope,n) {
  const at={start:n.start,end:n.end},name=text=>({kind:"name",name:text,...at});
  const implicit=n.section.params.filter(p=>p.implicit),explicit=n.section.params.filter(p=>!p.implicit);
  let inner=scope;
  for(const declared of n.section.declared) {
    if(!scope.env.has(declared)||scope.env.get(declared)?.tag==="Untranslated")continue;
    inner=inner.alias(declared,t.term({kind:"call",fn:name(declared),args:explicit.map(p=>name(p.name.text)),
      ...(implicit.length?{implicitArgs:implicit.map(p=>name(p.name.text))}:{}),...at},scope,null));
  }
  for(const p of n.section.params)if(p.type)inner=opened(t,inner,name(p.name.text),{complete:false})??inner;
  return inner;
}
