// The named syntax children and binder positions shared by term operations.
// Interval formulas, universe levels and system pieces have their own shapes.
//
// A term has two views, and every walk over terms names the one it reads.
// The kernel view is everything the kernel term mentions, a checked path
// application's annotation (pathType, the kernel's record of its path's
// type) included: scope, encoding, substitution and renaming read it, and so
// do the free names and dimensions a scope check reads (termChildren,
// termFields, termParts; freeNames). The written view is the syntax as
// written, annotations left out: matching and determinacy, unification and
// pattern walks, keys built from syntax, display, inspection and digests
// read it (writtenChildren, writtenFields, writtenParts; writtenNames).
export const termChildren = {
  U:[], Var:[], DefRef:[], Unit:[], Point:[],
  Pi:["domain","body"], Lam:["domain","body"], Sigma:["domain","body"],
  App:["fn","arg"], Pair:["as","first","second"], Fst:["pair"], Snd:["pair"],
  Path:["family","left","right"], PLam:["family","body"], PApp:["path","pathType"],
  Comp:["family","base"], HComp:["family","base"], Trans:["family","base"], Void:[], Abort:["as","impossible"],
  Sum:["left","right"], Inl:["as","value"], Inr:["as","value"],
  SumRec:["motive","left","right","value"], UnitRec:["motive","point","value"],
  Glue:["base"], GlueTerm:["as","base"], Unglue:["as","value"],
  LPi:["body"], LLam:["body"], LApp:["fn"], LBound:[],
  // Declared types (H1): an instance's parameters and an eliminator's
  // clauses are lists; an instance's recorded levels are levels.
  Sort:["parameters"], Con:["sort"], Elim:["motive","clauses"],
};
// The fields of the kernel view the written view leaves out.
export const annotationFields = new Set(["pathType"]);
export const writtenChildren = Object.fromEntries(Object.entries(termChildren)
  .map(([tag, keys]) => [tag, keys.filter(key => !annotationFields.has(key))]));
// A syntax object's fields, [key, value], and their values, in each view:
// for walks that read every field of terms and of the arrays and records
// inside them.
export const termFields = value => Object.entries(value);
export const writtenFields = value => Object.entries(value).filter(([key]) => !annotationFields.has(key));
export const termParts = value => Object.values(value);
export const writtenParts = value => writtenFields(value).map(([, part]) => part);
export const termBinders = new Set(["Pi", "Lam", "Sigma", "LPi", "LLam"]);
// In a composition system, only each piece's term is under the dimension;
// its face stays outside. Motive traversal matches term objects, not faces.
export const dimensionScope = new Map([["Path", ["family"]], ["PLam", ["family", "body"]],
  ["Comp", ["family", "system"]], ["HComp", ["system"]], ["Trans", ["family"]]]);
