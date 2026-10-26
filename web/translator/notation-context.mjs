// A checked notation effect is an ephemeral elaboration value. Canonical
// syntax retains only the identity of the activation/operand parameter that
// supplies it; neither live environments nor spelling lookups are serialized.
export const operatorBinding = operator => "\u0000operator " + operator;
export const SELECTION = "\u0000selection";
export const NUMERAL_NAT="\u0000notation UNat";
export function lexemeKey(name) { return "\u0000lexeme "+name; }
export const notationContextKey = key => "\u0000notation context " + key;

export const notationBinding=name=>"\u0000notation "+name;

// Display a value in the checked selection, never by a spelling alone: its
// notation's name and identity, a model's or the one a model's module added
// rules to, and the model whose notation it is. This is the one place the
// printer learns the scope it prints for (cubical-source-text.mjs), and
// what name.(…) selects there, as theories.mjs's selected decides it: a
// named notation first, then a model's notation, with the rules its module
// added where the name is still that model. A scope with a retained lexical
// context resolves names through it (LexicalContext.selector); one without
// resolves them by label. Either answers undefined where it cannot tell.
export function notationForScope(scope) {
  const selected=scope.env.get(SELECTION),env=scope.env,lexical=scope.lexical;
  // The named notation name.(…) selects, or the model value with the
  // identity of the notation its module attached where that applies.
  const selector=name=>{
    if(lexical) {
      let found;
      try {found=lexical.selector(name).value;}
      catch {return undefined;}
      return found.tag==="notation"?{identity:found.id,named:!found.model}
        :found.tag==="binding"?{binding:found.id}:found.tag==="missing"?null:undefined;
    }
    const notation=env.get(notationBinding(name)),value=env.get(name);
    if(notation?.tag==="Notation"&&!notation.model)return {identity:notation.bindingId??null,named:true};
    if(notation?.tag==="Notation"&&value===notation.model)return {identity:notation.bindingId??null,value};
    return value===undefined?null:{value};
  };
  return {selection:selected?.name??null,selectionIdentity:selected?.identity??selected?.extension??null,
    selectionReceiver:selected?.receiver??null,
    // The identity of the notation name.(…) selects: null where it selects
    // none, undefined where the scope cannot tell.
    reads:name=>{const found=selector(name);return found===undefined?undefined:found?.identity??null;},
    // Whether name.(…) opens `model`, a variable or a declared model, with
    // its theory's notation: no named notation takes the name, and a
    // declared model is still the name's value.
    opens:(name,model)=>{
      const found=selector(name);
      if(found===undefined)return undefined;
      if(found?.named)return false;
      if(model.tag==="Var")return true;
      if(found?.identity!==undefined)return false;
      if(lexical)return found?.binding!==undefined&&found.binding===scope.checker?.compilationBindings?.ofValue(model)?.id;
      return found?.value?.tag==="DefRef"&&found.value.name===model.name;
    }};
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
