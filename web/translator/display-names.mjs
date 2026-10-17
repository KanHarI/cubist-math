import { termBinders } from "./term-shape.mjs";

// One display pass's free-variable analysis. Unlike the checker's strict
// term analysis, it accepts display-only nodes and records containing terms.
// Its cache lasts only for the pass; display records need not be immutable.
// Returned sets belong to the cache and callers must not change them.
export function displayFreeNames() {
  const memo = new WeakMap(), empty = new Set();
  const free = value => {
    if (!value || typeof value !== "object") return empty;
    if (memo.has(value)) return memo.get(value);
    const names = new Set();
    memo.set(value, names);
    if (value.tag === "Var") names.add(value.name);
    else for (const [key, child] of Object.entries(value))
      for (const name of free(child))
        if (!(termBinders.has(value.tag) && key === "body" && name === value.name)) names.add(name);
    return names;
  };
  return free;
}
