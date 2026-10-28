// A checked notation effect is an ephemeral elaboration value. Canonical
// syntax retains only the identity of the activation/operand parameter that
// supplies it; neither live environments nor spelling lookups are serialized.
export const operatorBinding = operator => "\u0000operator " + operator;
export const SELECTION = "\u0000selection";
export const NUMERAL_NAT="\u0000notation UNat";
export function lexemeKey(name) { return "\u0000lexeme "+name; }
export const notationContextKey = key => "\u0000notation context " + key;

export const notationBinding=name=>"\u0000notation "+name;

// What name.(…), or use name, selects in an environment, as theories.mjs's
// selected decides it, which reads it here: a named notation first;
// otherwise the name's value, with the notation its model's module attached
// where the name is still that model.
export function selectionTarget(env,key) {
  const notation=env.get(notationBinding(key));
  if(notation?.tag==="Notation"&&!notation.model)return {named:notation};
  const value=env.get(key);
  return {value,attached:notation?.tag==="Notation"&&notation.model&&value!==undefined&&value===notation.model?notation:null};
}

// Display a value in the checked selection, never by a spelling alone: its
// notation's name and identity, a model's or the one a model's module added
// rules to, and the model whose notation it is. This is the one place the
// printer learns the scope it prints for (cubical-source-text.mjs): what
// name.(…) selects there, resolved as the elaborator resolves it in that
// very scope. A scope with a retained lexical context resolves the name
// through it (LexicalContext.selector), deciding a slot or an opening by the
// scope's outcomes; one without, through its environment (selectionTarget),
// whose model openings are aliases of the names they open. Each lookup costs
// a few map reads. A lookup answers undefined where the scope cannot tell,
// and the printer then prints no abbreviation. `namedOnly` restricts what
// an environment answers where an opening use was not applied to it: only
// named notations, which no opening hides.
export function notationContext({env,lexical=null,slotOutcomes=null,checker=null},selected,{namedOnly=false}={}) {
  const selector=name=>{
    if(lexical) {
      let found;
      try {
        found=lexical.selector(name).value;
        if(slotOutcomes&&["slot","opening","member","application"].includes(found.tag))found=slotOutcomes.resolve(found);
      } catch {return undefined;}
      return found.tag==="notation"?{identity:found.id,named:!found.model}:found.tag==="binding"?{binding:found.id}
        :found.tag==="missing"?null:found.tag==="member"?{member:true}:undefined;
    }
    const target=selectionTarget(env,name);
    if(target.named)return {identity:target.named.bindingId??null,named:true};
    if(namedOnly)return undefined;
    if(target.attached)return {identity:target.attached.bindingId??null,value:target.value};
    return target.value===undefined?null:{value:target.value};
  };
  return {selection:selected?.name??null,selectionIdentity:selected?.identity??selected?.extension??null,
    selectionReceiver:selected?.receiver??null,
    // The identity of the notation name.(…) selects: null where it selects
    // none, undefined where the scope cannot tell.
    reads:name=>{const found=selector(name);return found===undefined?undefined:found?.identity??null;},
    // Whether name.(…) opens `model`, a variable or a declared model, with
    // its theory's notation. No named notation takes the name. A variable
    // the printed text binds shadows any other value of its name; a free
    // one is named apart by display naming, so the name must not reach a
    // model's notation instead. A declared model must still be the name's
    // value, with no notation its module attached.
    opens:(name,model,boundInText)=>{
      const found=selector(name);
      if(found===undefined)return false;
      if(found?.named)return false;
      if(model.tag==="Var")return boundInText||found?.identity===undefined;
      if(found?.identity!==undefined)return false;
      if(found?.binding!==undefined)return found.binding===checker?.compilationBindings?.ofValue(model)?.id;
      return found?.value?.tag==="DefRef"&&found.value.name===model.name;
    }};
}

export const notationForScope=scope=>notationContext({env:scope.env,lexical:scope.lexical,
  slotOutcomes:scope.slotOutcomes,checker:scope.checker},scope.env.get(SELECTION));

// The selection file-level uses make, read from the module's environment as
// selected reads it, without elaborating them: a declaration's messages
// print in it before its own scope is entered, and terms shown after a
// module whose final scope could not be entered in its uses (with no
// notation selected). A use that names no named notation opens a model,
// whose fields the environment does not hold: after one, only named
// notations are known, and the receiver of a later model selection is not.
export function notationForUses(env,checker,uses,{select=true}={}) {
  let opening=false,selected=null;
  for(const use of uses??[]) {
    const name=use?.kind==="name"?use.name:null,target=name?selectionTarget(env,name):null;
    if(target?.named)selected={name,identity:target.named.bindingId??null};
    else {
      selected=name&&!opening?{name,receiver:target.value??null,...(target.attached?{extension:target.attached.bindingId??null}:{})}:null;
      opening=true;
    }
  }
  return notationContext({env,checker},select?selected:null,{namedOnly:opening});
}

export function checkedNotationContext(scope) {
  const selection=scope.env.get(SELECTION);
  if(!selection?.complete)throw new TypeError("A retained notation context requires a complete checked selection.");
  const aliases=[[SELECTION,selection],...[...selection.operators].map(operator=>
    [operatorBinding(operator),scope.env.get(operatorBinding(operator))])];
  return Object.freeze(aliases.map(Object.freeze));
}

export const notationContextEntry=(key,aliases)=>Object.freeze([notationContextKey(key),aliases]);
export const bindNotationContext=(scope,key)=>scope.aliases([notationContextEntry(key,checkedNotationContext(scope))]);

export function selectNotationContext(scope,key) {
  const aliases=scope.env.get(notationContextKey(key));
  if(!aliases)throw new TypeError("A retained notation use has no checked context for its identity.");
  const inner=scope.aliases(aliases),binding=scope.unit.bindingAdapter?.bindingForKey(key);
  return inner.lexical&&binding?inner.with({lexical:inner.lexical.withSelectedNotation(binding.id)}):inner;
}
