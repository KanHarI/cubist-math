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
// context resolves names through it (LexicalContext.selector), deciding a
// slot or an opening by the scope's outcomes; one without resolves them by
// label. Either answers undefined where it cannot tell, and the printer then
// prints no abbreviation.
export function notationContext({env,lexical=null,slotOutcomes=null,checker=null},selected) {
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
      if(lexical)return found?.binding!==undefined&&found.binding===checker?.compilationBindings?.ofValue(model)?.id;
      return found?.value?.tag==="DefRef"&&found.value.name===model.name;
    }};
}

export const notationForScope=scope=>notationContext({env:scope.env,lexical:scope.lexical,
  slotOutcomes:scope.slotOutcomes,checker:scope.checker},scope.env.get(SELECTION));

// The selection a declaration's file-level uses make, read from the
// module's environment as selected reads it, without elaborating them: a
// declaration's messages print in it before its own scope is entered.
export function notationForUses(env,checker,uses) {
  const use=uses?.at(-1),name=use?.kind==="name"?use.name:null;
  let selected=null;
  if(name) {
    const notation=env.get(notationBinding(name)),value=env.get(name);
    selected=notation?.tag==="Notation"&&!notation.model?{name,identity:notation.bindingId??null}
      :{name,receiver:value??null,...(notation?.tag==="Notation"&&value!==undefined&&notation.model===value
        ?{extension:notation.bindingId??null}:{})};
  }
  return notationContext({env,checker},selected);
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
