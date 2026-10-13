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
