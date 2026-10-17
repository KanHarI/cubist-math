// The named syntax children and binder positions shared by term operations.
// Interval formulas, universe levels and system pieces have their own shapes.
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
export const termBinders = new Set(["Pi", "Lam", "Sigma", "LPi", "LLam"]);
// In a composition system, only each piece's term is under the dimension;
// its face stays outside. Motive traversal matches term objects, not faces.
export const dimensionScope = new Map([["Path", ["family"]], ["PLam", ["family", "body"]],
  ["Comp", ["family", "system"]], ["HComp", ["system"]], ["Trans", ["family"]]]);
