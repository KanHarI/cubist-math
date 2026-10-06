// Notation's refusals in elaboration (L2.10a, L2.10b): an operator that the
// selected notation does not bind, one used where no notation is selected,
// and negation's. Their codes are E9's (web/diagnostics.mjs).

// An operator the selected notation does not bind.
export const unboundOperator = (selection, operator) =>
  Error(`${operator} is not in ${selection.name}'s notation, which is selected here: select a notation that binds it, as nat.(x ${operator} y), or write the operation.`);

// An operator that no name-based reading gives, used with no selection.
export const unselectedOperator = operator =>
  Error(`x ${operator} y means what a selected notation binds ${operator} to: select one, as integers.(x ${operator} y).`);

// -x with no selection, and with one that binds no negation.
export const unselectedNegation = () =>
  Error("-x negates in a selected notation that binds it, as integers.(-x); a path's reversal is ~p.");
export const unboundNegation = selection =>
  Error(`-x is not in ${selection.name}'s notation, which is selected here: select a notation that binds it, as integers.(-x).`);
