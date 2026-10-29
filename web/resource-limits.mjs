// An interrupted computation is not a negative answer to a typing query.
// Keep this classification shared by search, replay and contract checks.
// A "fault" is the kernel's instance failing (KernelFault in
// cubical-kernel.mjs): no answer at all.
const limits = new Set(["fuel", "budget", "deadline", "resource", "fault"]);
export const isResourceLimit = kind => limits.has(kind);
