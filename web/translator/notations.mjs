// Notation's refusals in elaboration (L2.10a, L2.10b): an operator that the
// selected notation does not bind, one used where no notation is selected,
// and negation's. Their codes are E9's (web/diagnostics.mjs).

// An operator the selected notation does not bind.
export const unboundOperator = (selection, operator) =>
  Error(`${operator} is not in ${selection.name}'s notation, which is selected here: select a notation that binds it, as nat.(x ${operator} y), or write the operation.`);

// An operator used with no selection (L2.10j): one that nat binds, as + or
// x > y, suggests nat.
const natural = new Set(["+", "*", "<", "<=", ">", ">="]);
export const unselectedOperator = operator => natural.has(operator)
  ? Error(`x ${operator} y means what a selected notation binds ${operator} to: for natural numbers, use nat; or write nat.(x ${operator} y).`)
  : Error(`x ${operator} y means what a selected notation binds ${operator} to: select one, as integers.(x ${operator} y).`);

// -x with no selection, and with one that binds no negation.
export const unselectedNegation = () =>
  Error("-x negates in a selected notation that binds it, as integers.(-x); a path's reversal is ~p.");
export const unboundNegation = selection =>
  Error(`-x is not in ${selection.name}'s notation, which is selected here: select a notation that binds it, as integers.(-x).`);

// A literal no selected notation reads, one its parser refuses, and one
// whose parse does not evaluate to an answer (L2.10c). A binary literal's
// notation is the archive's binary (binary_naturals).
export const literalUnread = (selection, text) => {
  const binary = /^0b/.test(text);
  if (!selection?.complete) return binary
    ? Error(`${text} is a binary literal, which a selected notation's literal rule reads, as the archive's binary.(${text}).`)
    : Error(`${text} is a literal that a selected notation's literal rule reads, as rationals.(${text}).`);
  if (/^[0-9]+$/.test(text))
    return Error(`${selection.name}'s notation reads no numeral ${text}: write nat.(${text}) for a natural number, or select a notation that reads it.`);
  return binary
    ? Error(`${selection.name}'s notation reads no binary literal ${text}: select one whose literal rule reads it, as the archive's binary.(${text}).`)
    : Error(`${selection.name}'s notation reads no literal ${text}: select a notation whose literal rule reads it, as rationals.(${text}).`);
};
export const literalRefused = (selection, text, position) =>
  Error(`${selection.name}'s literal rule refuses ${text} at its character ${position + 1}.`);
export const literalUnevaluated = (selection, text, answer) =>
  Error(`${selection.name}'s literal rule does not evaluate ${text} to an answer; it gives ${answer}.`);

// A numeral or a literal where no notation is selected (L2.10j).
export const unselectedLiteral = text => /^[0-9]+$/.test(text)
  ? Error(`${text} means the natural number in a selected notation that reads it: use nat; or write nat.(${text}).`)
  : literalUnread(null, text);
