// A checked notation effect is an ephemeral elaboration value. Canonical
// syntax retains only the identity of the activation/operand parameter that
// supplies it; neither live environments nor spelling lookups are serialized.
export const operatorBinding = operator => "\u0000operator " + operator;
export const SELECTION = "\u0000selection";
const contextKey = key => "\u0000notation context " + key;

export function bindNotationContext(scope,key) {
  const selection=scope.env.get(SELECTION);
  if(!selection?.complete)throw new TypeError("A retained notation context requires a complete checked selection.");
  const aliases=[[SELECTION,selection],...[...selection.operators].map(operator=>
    [operatorBinding(operator),scope.env.get(operatorBinding(operator))])];
  return scope.alias(contextKey(key),Object.freeze(aliases.map(Object.freeze)));
}

export function selectNotationContext(scope,key) {
  const aliases=scope.env.get(contextKey(key));
  if(!aliases)throw new TypeError("A retained notation use has no checked context for its identity.");
  return scope.aliases(aliases);
}
