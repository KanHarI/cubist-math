// The one supply of generated names for an elaboration unit: a source module.
// The elaborator, its rewriting service and its
// checker queries all draw binder names from the unit's supply, so no two
// generated names in a unit are equal. Each unit starts its own serial, so
// elaborating the same source again yields the same names. Units produce
// closed definitions, so names from different units never meet.
// A generated name never equals an assumption (`taken`) or a symbol that the
// kernel creates itself, which the adapter spells native<id>. Stand-alone
// syntax builders (equivalence.mjs, path-algebra.mjs and their users) take no
// supply: they avoid every name in their inputs, and their stems never end in
// a digit, unlike every name here.
export class NameSupply {
  constructor({taken = () => false} = {}) {
    this.serial = 0;
    this.taken = taken;
  }
  // A stem that ends in a digit gets a separator: otherwise a1 with serial 1
  // and a with serial 11 would both be a11, and one binder would capture the
  // other. So does the stem native, which would spell a kernel symbol, and a
  // stem of U's, which would spell a universe constant such as U1 or UU0.
  fresh(stem = "b") {
    const base = /[0-9]$/.test(stem) || stem === "native" || /^U+$/.test(stem) ? `${stem}_` : stem;
    let name;
    do name = `${base}${++this.serial}`; while (this.taken(name));
    return name;
  }
}

// How the display shows a kernel name (web/cubical-elaborator.mjs,
// web/cubical-source-text.mjs). These rules are defined here once: the
// printer applies them, and code that must predict what it prints, such as
// an inspection view choosing names new to everything it shows, derives its
// predictions from them.
//
// A module's definition is module__local, and shows its local name. A name
// that starts with __, such as an assumption's, has no module.
export const localName = name => name.includes("__") && !name.startsWith("__") ? name.slice(name.indexOf("__") + 2) : name;
// A variable shows its stem: a generated name without its serial, n for n11,
// and U for U_1, whose separator only keeps it apart from the constant U1. A
// kernel symbol, native<id>, shows x.
export const stem = name => name.startsWith("__") ? name : /^native\d+$/.test(name) ? "x"
  : name.replace(/\d+$/, "").replace(/^(U+)_$/, "$1") || name;
// Two variables that would show alike are told apart by numbering the stem
// from 1. Names such as U3 and UU0 spell universe constants (G0 §1.4), so the
// U stem numbered 1 shows as U_1. Every numbered name ends in a digit.
export const numberedName = (base, index) => /^U+$/.test(base) ? `${base}_${index}` : `${base}${index}`;
// Every form a name may show in, apart from a numbered one. The display
// gives a variable its stem, or leaves it, and the printer shows a free
// variable or a definition by its local name: so the name, its stem, and
// the local name of either.
export const printedForms = name => [...new Set([name, stem(name)].flatMap(form => [form, localName(form)]))];
// A name the display shows as it is wherever it occurs: its own stem and
// local name, and no numbered name.
export const printsAsItself = name => stem(name) === name && localName(name) === name && !/\d$/.test(name);
