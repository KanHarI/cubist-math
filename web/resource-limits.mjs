// An interrupted computation is not a negative answer to a typing query.
// Keep this classification shared by search, replay and contract checks.
const limits = new Set(["fuel", "budget", "deadline", "resource"]);
export const isResourceLimit = kind => limits.has(kind);
