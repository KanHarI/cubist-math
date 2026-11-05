// Kernel syntax written with names, for tests that build terms node by node.
// Since ABI 4 a binder carries no name and a variable is a bound index or an
// entry (docs/roadmaps/kernel/locally-nameless-kernel.md, section 3.1), so a
// term is written here as a function of the names of the binders around it,
// and made kernel syntax at the end (`realize`): a name an enclosing binder
// binds is that binder's index, and any other name is an entry made for it,
// a term entry of type Unit (`v`) or a level entry (`lv`), the same entry
// for the same name each time.
import { InstructionGraph } from "../web/cubical-instructions.mjs";

export function namedTerms(kernel) {
  const graph = new InstructionGraph(kernel), entries = new Map(), levels = new Map();
  const realize = (part, around = []) => typeof part === "function" ? part(around) : part;
  const variable = (name, made, make) => around => {
    const index = around.indexOf(name);
    if (index >= 0) return kernel.term("Bound", index);
    if (!made.has(name)) made.set(name, make(String(name)));
    return kernel.term("Context", made.get(name));
  };
  return {
    realize,
    // A node over its children, each a handle or a part still to realize.
    term: (kind, payload, ...children) => around => kernel.term(kind, payload, ...children.map(child => realize(child, around))),
    // A term or level binder binding `name` in its body, not in its domain.
    bind: (kind, name, domain, body) => around => kernel.term(kind, 0, realize(domain, around), realize(body, [name, ...around])),
    v: name => variable(name, entries, spelling => graph.extend(graph.unit(), spelling)),
    lv: name => variable(name, levels, spelling => graph.level(spelling)),
    // The entry a free name was made, making it if need be.
    entry: name => { realize(variable(name, entries, spelling => graph.extend(graph.unit(), spelling))); return entries.get(name); },
  };
}
