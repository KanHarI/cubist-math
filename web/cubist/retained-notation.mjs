// A model notation's operand receivers belong to the field declaration's
// surrounding interface, outside the formal operand binders. The receiver
// syntax stays open over that interface until a checked model supplies it.
import {resolveBindingReceiver,cloneBindingSyntax,remapBindingSyntax,sameBindingSyntax} from "./binding-syntax.mjs";
import {notationKey,notationViews,validateFieldNotation} from "./theory-notation.mjs";
import {parentNamespaceFailure} from "./retained-interfaces.mjs";

export function retainFieldNotation(item,entry,fields,options) {
  if(!item.notation)return null;
  const parameters=entry.syntax.tree.params.filter(p=>!p.name.synthetic);
  const {key}=validateFieldNotation(item,{theory:options.theory,isCarrier:k=>{
    const type=options.domains?.get(parameters[k]?.name.bindingId)??parameters[k]?.type;
    return type?.kind==="bindingReference"&&type.resolution.tag==="binding"
      &&fields.some(field=>field.id===type.resolution.id&&field.kind==="sort");
  }});
  // The source producer resolves receivers before admitting the operation.
  // Validation consumes that recipe; it cannot reconstruct a source scope.
  const {recipe}=options;
  if(!recipe)throw new TypeError("A field notation needs its source-resolved operand recipe.");
  return Object.freeze({key,field:entry.id,recipe});
}

export function retainOperandRecipe(views,context,options) {
  const receiver=(token,side)=>token?resolveBindingReceiver({kind:"name",name:token.text,...token},{
    ...options,owner:[...options.owner,side],context,
    namespaceFailure:error=>parentNamespaceFailure(options.theory,error),
  }):null;
  return Object.freeze({left:receiver(views.left,"left"),right:receiver(views.right,"right")});
}

// The operation and both operand receivers determine a notation's meaning.
// In particular, sharing an ancestor operation does not justify selecting
// one of two different operand recipes according to parent enumeration order.
export function sameRetainedNotation(left,right) {
  return left.field===right.field&&["left","right"].every(side=>{
    const a=left.recipe[side],b=right.recipe[side];
    return a&&b?sameBindingSyntax(a,b):a===b;
  });
}

export function inheritNotations(parents,options) {
  const {table,owner,context}=options;
  const candidates=new Map(),namespaceNotations={};let serial=0;
  const add=(own,key,value)=>{
    for(const target of [candidates,own]) {
      if(!target.has(key))target.set(key,[]);
      const list=target.get(key);
      if(!list.some(existing=>sameRetainedNotation(existing,value)))list.push(value);
    }
  };
  const finish=candidates=>{
    const notationBindings={},ambiguousNotationBindings={},ambiguousNotations={};
    for(const [key,list] of candidates) {
      if(list.length===1) {
        const {path,parentField,call,...rule}=list[0];notationBindings[key]=Object.freeze(rule);
      } else {
        ambiguousNotationBindings[key]=Object.freeze(list);
        ambiguousNotations[key]=Object.freeze(list.map(rule=>Object.freeze({label:rule.path.join("."),
          field:table.get(rule.field).label,parentField:rule.parentField,...(rule.call?{call:true}:{})})));
      }
    }
    return {notationBindings,ambiguousNotationBindings:Object.freeze(ambiguousNotationBindings),
      ambiguousNotations:Object.freeze(ambiguousNotations)};
  };
  for(const parent of parents) {
    const own=new Map();
    const {record,correspondence}=parent;
    if(Object.keys(record.notations??{}).length&&!record.notationBindings
      ||Object.keys(record.ambiguousNotations??{}).length&&!record.ambiguousNotationBindings)
      throw new TypeError("Inherited notation requires its retained binding interface.");
    const inherit=(rule,path,parentField)=>{
      if(!correspondence.has(rule.field))throw new TypeError("An inherited notation is missing its operation correspondence.");
      const receiver=syntax=>syntax?remapBindingSyntax(cloneBindingSyntax(syntax,table,[...owner,"notation",String(serial++)],
        {expansion:{kind:"inheritance",site:parent.site}}).syntax,table,correspondence):null;
      return Object.freeze({...rule,field:correspondence.get(rule.field),
        recipe:Object.freeze({left:receiver(rule.recipe.left),right:receiver(rule.recipe.right)}),
        path:Object.freeze(path),parentField});
    };
    for(const [key,rule] of Object.entries(record.notationBindings??{}))if(!parent.renotated.has(rule.field))
      add(own,key,inherit(rule,[parent.label],table.get(rule.field).label));
    for(const [key,list] of Object.entries(record.ambiguousNotationBindings??{}))for(const rule of list)
      if(!parent.renotated.has(rule.field))add(own,key,inherit(rule,[parent.label,...rule.path],rule.parentField));
    // A replacement annotation belongs to the child interface formed by
    // extends. Its receiver is resolved once there, after field renaming,
    // independently of both the parent's recipe and the pattern operands.
    for(const [field,rename] of parent.renotated) {
      const key=notationKey(rename.notation);
      add(own,key,Object.freeze({key,field:correspondence.get(field),
        recipe:retainOperandRecipe(notationViews(rename.notation),context,{...options,owner:[...owner,"renotation",String(serial++)]}),
        path:Object.freeze([parent.label]),parentField:table.get(field).label,call:true}));
    }
    const selected=finish(own);
    namespaceNotations[parent.label]=Object.freeze({name:record.name,bindings:selected.notationBindings,
      ambiguous:selected.ambiguousNotations});
  }
  return {...finish(candidates),namespaceNotations:Object.freeze(namespaceNotations)};
}
