// A checked notation effect is an ephemeral elaboration value. Canonical
// syntax retains only the identity of the activation/operand parameter that
// supplies it; neither live environments nor spelling lookups are serialized.
export const operatorBinding = operator => "\u0000operator " + operator;
export const SELECTION = "\u0000selection";
export const NUMERAL_NAT="\u0000notation Nat";
export function lexemeKey(name) { return "\u0000lexeme "+name; }
export const notationContextKey = key => "\u0000notation context " + key;

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
  return scope.aliases(aliases);
}
