import { isResourceLimit } from "../resource-limits.mjs";

// A synchronous replay callback ends the containing elaboration after it has
// serialized its result. This is control flow, never a source diagnostic or
// an invitation to try another elaboration strategy. The program boundary
// still rolls back the live transaction before the coordinator disposes it.
export class ElaborationStop {
  constructor(result) {
    this.result = result;
    Object.freeze(this);
  }
}

export function propagateElaborationStop(value) {
  if (value instanceof ElaborationStop) throw value;
}

// A refusal no other elaboration of the same source can answer: the source
// wrote what it may not write, as a legacy builtin outside the archive
// (builtins.mjs, legacyConfinement). It is a diagnostic, never a failed
// attempt: a speculative elaboration that meets it reports it, rather than
// trying another strategy or saying that nothing determines an argument.
export class SourceRefusal extends Error {}
export function propagateRefusal(value) {
  if (value instanceof SourceRefusal) throw value;
}

// A failed speculative check is no answer when elaboration was interrupted,
// or when the source was refused.
export function propagateLimit(value) {
  propagateElaborationStop(value);
  propagateRefusal(value);
  if (isResourceLimit(value?.kind)) throw value;
}
