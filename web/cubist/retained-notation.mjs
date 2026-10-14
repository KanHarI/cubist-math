// A model notation's operand receivers belong to the field declaration's
// surrounding interface, outside the formal operand binders. The receiver
// syntax stays open over that interface until a checked model supplies it.
import {LexicalContext} from "./bindings.mjs";
import {resolveBindingSyntax} from "./binding-syntax.mjs";
import {validateFieldNotation} from "./theory-notation.mjs";

export function retainFieldNotation(item,entry,fields,options) {
  if(!item.notation)return null;
  const parameters=entry.syntax.tree.params.filter(p=>!p.name.synthetic);
  const key=validateFieldNotation(item,{theory:options.theory,isCarrier:k=>{
    const type=parameters[k]?.type;
    return type?.kind==="bindingReference"&&type.resolution.tag==="binding"
      &&fields.some(field=>field.id===type.resolution.id&&field.kind==="sort");
  }});
  const context=new LexicalContext(entry.lexical);
  const receiver=(token,side)=>token?resolveBindingSyntax({kind:"name",name:token.text,...token},{
    ...options,owner:[...options.owner,"notation",entry.id,side],context,
  }):null;
  const recipe=Object.freeze({left:receiver(item.notation.leftView,"left"),right:receiver(item.notation.rightView,"right")});
  return Object.freeze({key,field:entry.id,recipe});
}
