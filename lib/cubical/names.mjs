// The one supply of generated names for an elaboration unit: a source module,
// or one template inspection. The elaborator, its rewriting service and its
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
  // other. So does the stem native, which would spell a kernel symbol.
  fresh(stem = "b") {
    const base = /[0-9]$/.test(stem) || stem === "native" ? `${stem}_` : stem;
    let name;
    do name = `${base}${++this.serial}`; while (this.taken(name));
    return name;
  }
}
