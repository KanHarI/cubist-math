// Deterministic homogeneous rewriting through ordinary applications only.
// Every candidate context and resulting witness is checked by the C kernel.
// Each function works at an elaboration scope (elaboration.mjs): its checker
// queries, generated names and work counters are the scope's.
import {T,levelNames} from "./core.mjs";
import {interval as I} from "./lattice.mjs";
import {freeDimensions} from "./dimension-slots.mjs";

// A bounded search gave up: too many nodes, candidates or rewrites, a cycle,
// or a term too large to compare. Speculative callers such as premise search
// contain it. Running out of the search's fuel (fuel.mjs, spent through the
// scope's unit) is SearchFuelExhausted instead: the whole search shares the
// fuel, so such callers do not contain it.
export class SearchLimit extends Error {}

const replacement = (term, path, value) => {
  if (!path.length) return value;
  const [key, ...rest] = path;
  return { ...term, [key]: replacement(term[key], rest, value) };
};

// How a level variable occurs in a term (G0): bare, as the universe U(x) or
// an instantiation f(x), or inside a larger level such as next(x).
const levelOccurrence = (term, name) => {
  let bare = false, other = false;
  const seen = new WeakSet();
  const walk = t => {
    if (!t || typeof t !== "object" || seen.has(t)) return;
    seen.add(t);
    if ((t.tag === "U" || t.tag === "LApp") && typeof t.level === "object" && levelNames(t.level).has(name)) {
      if (t.level.tag === "Var" && t.level.name === name) bare = true; else other = true;
    }
    for (const child of Object.values(t)) walk(child);
  };
  walk(term);
  return {bare, other, any: bare || other};
};
// A level an instantiation accepts: below UU0 (G0 Q10).
const finiteLevel = level => typeof level === "number" || level?.tag === "Var"
  || (level?.tag === "LConst" && !level.tier) || (level?.tag === "LSucc" && finiteLevel(level.level))
  || (level?.tag === "LMax" && finiteLevel(level.left) && finiteLevel(level.right));

export function equalityRule(scope, term, reverse = false) {
  const type = scope.nf(scope.infer(term).type);
  // A universe-generic equality: rw matches its universe like simp does.
  if (type.tag === "LPi" && scope.nf(T.levelApply(T.levelLambda(type.name, type.body), 0)).tag === "Path")
    return simplificationRule(scope, term, reverse);
  if (type.tag !== "Path" || freeDimensions(type.family).has(type.dim))
    throw Error("rw requires a homogeneous equality proof.");
  if (!reverse) return {term, carrier:type.family, left:type.left, right:type.right};
  const dim = scope.fresh("rewrite_inverse");
  const reversed = T.line(dim, type.family, T.at(term, I.reverse(I.variable(dim))));
  const target = T.path(dim, type.family, type.right, type.left);
  const checked = scope.check(reversed, target);
  return {term:scope.ascribe(checked,target), carrier:type.family,
    left:type.right, right:type.left};
}

// Instantiate a first-order, rigid application pattern. A parameter must
// occur on the matched side; unmatched parameters remain explicit obligations.
// A candidate is instantiated at the scope of the search that meets it, which
// premise search also uses.
export function simplificationRule(scope, term, reverse = false, witnesses = [], solvePremise = null) {
  let type = scope.nf(scope.infer(term).type);
  if (type.tag === "Path") return equalityRule(scope, term, reverse);
  // A universe-generic rule (G0 §4.3) has one level, a pattern variable
  // matched only where the matched side has it bare: U or f(U).
  let level = null;
  if (type.tag === "LPi") {
    level = scope.fresh("simp_level");
    type = scope.nf(T.levelApply(T.levelLambda(type.name, type.body), T.variable(level)));
  }
  const parameters = [],domains=[];
  while (type.tag === "Pi") {
    const marker = scope.fresh("simp_parameter");
    parameters.push(marker);
    domains.push(type.domain);
    type = scope.nf(T.app(T.lam(type.name,type.domain,type.body),T.variable(marker)));
    if (parameters.length > 16) throw Error("Simplification rule has too many parameters.");
  }
  if (type.tag !== "Path" || freeDimensions(type.family).has(type.dim))
    throw Error("simp only requires homogeneous equality lemmas.");
  const pattern = reverse ? type.right : type.left;
  const markers = new Set(parameters);
  const present=new Set();
  const seen=new WeakSet();
  let visits=0;
  const collect=value=>{
    if(!value||typeof value!=="object"||seen.has(value))return;
    seen.add(value);
    scope.spend("nodes");
    if((++visits&255)===1)scope.checkDeadline();
    if(value.tag==="Var"&&markers.has(value.name))present.add(value.name);
    for(const child of Object.values(value))collect(child);
  };
  collect(pattern);
  // Otherwise the level is the least one that holds the arguments of
  // parameters A : U matched on that side; or, when neither the statement nor
  // a parameter mentions it, any level will do and U0 is used.
  let levelFrom=null;
  const levelDomains=[];
  if(level) {
    const onPattern=levelOccurrence(pattern,level);
    if(onPattern.other)
      throw Error("A universe-generic rule is matched only where its universe is a bare variable; supply its universe argument, as in lemma(U0).");
    if(onPattern.bare)levelFrom="match";
    else {
      for(let index=0;index<parameters.length;index++)
        if(present.has(parameters[index])&&domains[index].tag==="U"
          &&domains[index].level?.tag==="Var"&&domains[index].level.name===level)levelDomains.push(index);
      if(levelDomains.length)levelFrom="domains";
      else if(!levelOccurrence(type,level).any&&!domains.some(domain=>levelOccurrence(domain,level).any))levelFrom="any";
      else throw Error("A universe-generic rule's universe is not determined by the matched side; supply it, as in lemma(U0).");
    }
  }
  const premiseIndexes=new Set();
  for(let index=0;index<parameters.length;index++)if(!present.has(parameters[index])) {
    const domain=domains[index];
    if(domain.tag!=="Path"||freeDimensions(domain.family).has(domain.dim))
      throw Error("A simplification rule parameter is not determined by the matched side; supply arguments.");
    premiseIndexes.add(index);
  }
  // Universes match by level: the rule's level variable takes the subject's
  // level; any other level must be equal to it.
  const matchLevel = (at, shape, value, assignments) => {
    if (level && shape?.tag === "Var" && shape.name === level) {
      if (assignments.has(level)) return at.equal(T.universe(assignments.get(level)),T.universe(value));
      if (!finiteLevel(value)) return false;
      assignments.set(level,value);
      return true;
    }
    return at.equal(T.universe(shape),T.universe(value));
  };
  const match = (at, shape, value, assignments) => {
    if (shape.tag === "Var" && markers.has(shape.name)) {
      const previous = assignments.get(shape.name);
      if (previous) return at.equal(previous,value);
      assignments.set(shape.name,value);
      return true;
    }
    if (shape.tag !== value.tag) return false;
    if (shape.tag === "DefRef") return shape.name === value.name;
    if (shape.tag === "Var") return shape.name === value.name;
    if (["Zero","Nat","Unit","Void","Point"].includes(shape.tag)) return true;
    if (shape.tag === "Succ") return match(at,shape.value,value.value,assignments);
    if (shape.tag === "App") return match(at,shape.fn,value.fn,assignments)
      && match(at,shape.arg,value.arg,assignments);
    if (shape.tag === "U") return matchLevel(at,shape.level,value.level,assignments);
    if (shape.tag === "LApp") return match(at,shape.fn,value.fn,assignments)
      && matchLevel(at,shape.level,value.level,assignments);
    // A declared type's constructor, by its number and its instance; an
    // instance, by its signature, its parameters and its recorded levels.
    if (shape.tag === "Con") return shape.index === value.index && match(at,shape.sort,value.sort,assignments);
    if (shape.tag === "Sort") {
      const [parameters, levels] = [shape.parameters ?? [], shape.levels ?? []];
      return shape.signature === value.signature && parameters.length === (value.parameters ?? []).length
        && levels.length === (value.levels ?? []).length
        && parameters.every((parameter, index) => match(at,parameter,value.parameters[index],assignments))
        && levels.every((l, index) => matchLevel(at,l,value.levels[index],assignments));
    }
    return false;
  };
  let failure=null;
  const instantiate=(subject,at=scope)=>{
    const assignments = new Map();
    if (!match(at,pattern,subject,assignments)) return null;
    let applied = term;
    if (level) {
      let value = levelFrom === "match" ? assignments.get(level) : levelFrom === "any" ? 0 : null;
      for (const index of levelDomains) {
        const universe = at.nf(at.infer(assignments.get(parameters[index])).type);
        if (universe.tag !== "U") return null;
        value = value === null ? universe.level
          : typeof value === "number" && typeof universe.level === "number" ? Math.max(value,universe.level)
          : {tag:"LMax",left:value,right:universe.level};
      }
      if (!finiteLevel(value)) return null;
      applied = T.levelApply(term,value);
    }
    const premiseRules=[];
    for (const [index,marker] of parameters.entries()) {
      const pi = at.nf(at.infer(applied).type);
      if (pi.tag !== "Pi") throw Error("Simplification rule lost a parameter.");
      let arg=assignments.get(marker);
      if(!arg&&premiseIndexes.has(index)) {
        for(const witness of witnesses) {
          const checked=at.attempt(witness,pi.domain);
          if(checked.ok) {arg=checked.term;break;}
          if(checked.failure!=="mismatch")throw checked.error;
        }
        if(!arg) {
          const premise=at.nf(pi.domain);
          if(premise.tag==="Path"&&!freeDimensions(premise.family).has(premise.dim)
            &&at.equal(premise.left,premise.right)) {
            const dim=at.fresh("simp_premise");
            arg=at.check(T.line(dim,premise.family,premise.left),pi.domain);
          }
        }
        if(!arg&&solvePremise) {
          const solved=solvePremise(pi.domain,at);
          if(solved) {
            arg=solved.term;
            premiseRules.push(...solved.rules);
          }
        }
        if(!arg) {
          failure={kind:"premise",parameter:index+1};
          return null;
        }
      }
      // A rigid syntactic match can assign a parameter of the wrong type.
      // That candidate is ineligible; another rule may still apply here.
      if(!at.accepts(arg,pi.domain))return null;
      applied = T.app(applied,arg);
    }
    const concrete = equalityRule(at,applied,reverse);
    return at.equal(subject,concrete.left)
      ? {...concrete,premiseRules} : null;
  };
  return {clearDiagnostic() {failure=null;},diagnostic() {return failure;},instantiate};
}

// Search one endpoint for the requested eligible occurrence. Not finding one
// is an ordinary result, not an error: `eligible` counts the matches seen and
// `unsupported` records a match skipped because replacing it would change the
// result type (a dependent position). Each caller decides what that means.
export function findRewrite(scope, root, carrier, rule, occurrence = 1, order = "preorder") {
  if (!Number.isSafeInteger(occurrence) || occurrence < 1) throw Error("Invalid rewrite occurrence.");
  const work = scope.unit.work;
  work.traversals++;
  let visits = 0, candidates = 0, eligible = 0, unsupported = false;
  let found = null;
  const consider = (subject, path) => {
    if(++visits>512)throw new SearchLimit("Rewrite traversal budget exceeded.");
    scope.spend("visits");
    for(const candidate of Array.isArray(rule)?rule:[rule]) {
      work.candidateVisits++;
      if (++candidates > 8192) throw new SearchLimit("Rewrite candidate budget exceeded.");
      scope.spend("candidates");
      if (candidates % 16 === 0) scope.checkDeadline();
      try {
        const selected = candidate.instantiate?.(subject,scope)
          ?? (candidate.instantiate ? null : candidate);
        if (!selected || !scope.accepts(subject, selected.carrier)) continue;
        if (!scope.equal(subject, selected.left)) continue;
        const hole = scope.fresh("rewrite_hole");
        const variable = T.variable(hole);
        const contextTerm = T.lam(hole, selected.carrier, replacement(root, path, variable));
        if (!scope.accepts(contextTerm, T.pi(hole, selected.carrier, carrier))) {
          unsupported = true; continue;
        }
        eligible++;
        work.eligibleMatches++;
        if (eligible !== occurrence) continue;
        const after = replacement(root, path, selected.right);
        const dim = scope.fresh("rewrite_dim");
        const raw = T.line(dim, carrier, T.app(contextTerm, T.at(selected.term, I.variable(dim))));
        const target = T.path(dim, carrier, root, after);
        const checked = scope.check(raw, target);
        found = {after, witness:scope.ascribe(checked,target),
          occurrence:eligible, visits,premiseRules:selected.premiseRules??[],rule:candidate};
        work.successfulRewrites++;
        return;
      } catch(error) {
        error.rewriteRule??=candidate;
        throw error;
      }
    }
  };
  const visit = (term, path = []) => {
    if (found) return;
    if (order === "preorder") consider(term, path);
    if (found) return;
    if (term.tag === "App") {
      visit(term.fn, [...path, "fn"]);
      if (!found) visit(term.arg, [...path, "arg"]);
    }
    if (!found && order === "postorder") consider(term, path);
  };
  visit(root);
  return {found, eligible, unsupported};
}

// rw with an explicit endpoint: a missing occurrence is the user's error.
export function rewriteFirst(scope, root, carrier, rule, occurrence = 1, order = "preorder") {
  const {found, eligible, unsupported} = findRewrite(scope, root, carrier, rule, occurrence, order);
  if (found) return found;
  throw Error(unsupported ? "Rewrite match occurs in an unsupported dependent position."
    : `Rewrite occurrence ${occurrence} was not found (${eligible} eligible matches).`);
}
