// Deterministic homogeneous rewriting through ordinary applications only.
// Every candidate context and resulting witness is checked by the C kernel.
import {T} from "./core.mjs";
import {interval as I} from "./lattice.mjs";
import {freeDimensions} from "./dimension-slots.mjs";

// A bounded search gave up: too many nodes, candidates or rewrites, a cycle,
// or a term too large to compare. Speculative callers such as premise search
// contain it. SearchTimeout is the elapsed-time limit of the enclosing search,
// which such callers share and therefore do not contain.
export class SearchLimit extends Error {}
export class SearchTimeout extends Error {}

let serial = 0;
const namesIn = (term, result = new Set(), seen = new WeakSet()) => {
  if (!term || typeof term !== "object" || seen.has(term)) return result;
  seen.add(term);
  if (term.tag === "Var" || ["Pi","Lam","Sigma","W"].includes(term.tag))
    result.add(term.name);
  for (const value of Object.values(term)) {
    if (Array.isArray(value)) value.forEach(part => namesIn(part,result,seen));
    else if (value && typeof value === "object") namesIn(value,result,seen);
  }
  return result;
};
const freshName = (stem, terms, context, dimensions) => {
  const used = new Set([...context.keys(), ...dimensions.keys()]);
  for (const term of terms) {
    namesIn(term,used);
    for (const dim of freeDimensions(term)) used.add(dim);
  }
  let name;
  do { name = `${stem}_${++serial}`; } while (used.has(name));
  return name;
};
const replacement = (term, path, value) => {
  if (!path.length) return value;
  const [key, ...rest] = path;
  return { ...term, [key]: replacement(term[key], rest, value) };
};

export function equalityRule(checker, term, context, reverse = false) {
  const type = checker.nf(checker.infer(term, context).type);
  if (type.tag !== "Path" || freeDimensions(type.family).has(type.dim))
    throw Error("rw requires a homogeneous equality proof.");
  if (!reverse) return {term, carrier:type.family, left:type.left, right:type.right};
  const dim = freshName("rewrite_inverse",[term,type.family,type.left,type.right],context,checker.dimensions);
  const reversed = T.line(dim, type.family, T.at(term, I.reverse(I.variable(dim))));
  const target = T.path(dim, type.family, type.right, type.left);
  const checked = checker.check(reversed, target, context);
  return {term:checker.ascribe?.(checked,target)??checked, carrier:type.family,
    left:type.right, right:type.left};
}

// Instantiate a first-order, rigid application pattern. A parameter must
// occur on the matched side; unmatched parameters remain explicit obligations.
export function simplificationRule(checker, term, context, reverse = false, witnesses = [], solvePremise = null,
  deadline = performance.now() + 1000) {
  let type = checker.nf(checker.infer(term, context).type);
  if (type.tag === "Path") return equalityRule(checker, term, context, reverse);
  const parameters = [],domains=[];
  const occupied = new Set(context.keys());
  while (type.tag === "Pi") {
    let marker = `simp_parameter_${++serial}`;
    while (occupied.has(marker)) marker += "_";
    occupied.add(marker);
    parameters.push(marker);
    domains.push(type.domain);
    type = checker.nf(T.app(T.lam(type.name,type.domain,type.body),T.variable(marker)));
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
    if((++visits&255)===1) {
      if(performance.now()>deadline)throw new SearchTimeout("Simplification rule-pattern work budget exceeded.");
      checker.kernel?.checkDeadline();
    }
    if(value.tag==="Var"&&markers.has(value.name))present.add(value.name);
    for(const child of Object.values(value))collect(child);
  };
  collect(pattern);
  const premiseIndexes=new Set();
  for(let index=0;index<parameters.length;index++)if(!present.has(parameters[index])) {
    const domain=domains[index];
    if(domain.tag!=="Path"||freeDimensions(domain.family).has(domain.dim))
      throw Error("A simplification rule parameter is not determined by the matched side; supply arguments.");
    premiseIndexes.add(index);
  }
  const match = (shape, value, assignments) => {
    if (shape.tag === "Var" && markers.has(shape.name)) {
      const previous = assignments.get(shape.name);
      if (previous) return checker.equal(previous,value,context);
      assignments.set(shape.name,value);
      return true;
    }
    if (shape.tag !== value.tag) return false;
    if (shape.tag === "DefRef") return shape.name === value.name;
    if (shape.tag === "Var") return shape.name === value.name;
    if (["Zero","Nat","Unit","Point"].includes(shape.tag)) return true;
    if (shape.tag === "Succ") return match(shape.value,value.value,assignments);
    if (shape.tag === "App") return match(shape.fn,value.fn,assignments)
      && match(shape.arg,value.arg,assignments);
    return false;
  };
  let failure=null;
  const instantiate=(subject,deadline=performance.now()+1000)=>{
    const assignments = new Map();
    if (!match(pattern,subject,assignments)) return null;
    let applied = term;
    const premiseRules=[];
    for (const [index,marker] of parameters.entries()) {
      const pi = checker.nf(checker.infer(applied,context).type);
      if (pi.tag !== "Pi") throw Error("Simplification rule lost a parameter.");
      let arg=assignments.get(marker);
      if(!arg&&premiseIndexes.has(index)) {
        for(const witness of witnesses) {
          try {arg=checker.check(witness,pi.domain,context);break;}
          catch(error) {if(error.message!=="Type mismatch.")throw error;}
        }
        if(!arg) {
          const premise=checker.nf(pi.domain);
          if(premise.tag==="Path"&&!freeDimensions(premise.family).has(premise.dim)
            &&checker.equal(premise.left,premise.right,context)) {
            const dim=freshName("simp_premise",[premise,term],context,checker.dimensions);
            arg=checker.check(T.line(dim,premise.family,premise.left),pi.domain,context);
          }
        }
        if(!arg&&solvePremise) {
          const solved=solvePremise(pi.domain,deadline);
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
      try {checker.check(arg,pi.domain,context);}
      catch(error) {
        // A rigid syntactic match can assign a parameter of the wrong type.
        // That candidate is ineligible; another rule may still apply here.
        if(error.message==="Type mismatch.")return null;
        throw error;
      }
      applied = T.app(applied,arg);
    }
    const concrete = equalityRule(checker,applied,context,reverse);
    return checker.equal(subject,concrete.left,context)
      ? {...concrete,premiseRules} : null;
  };
  return {clearDiagnostic() {failure=null;},diagnostic() {return failure;},instantiate};
}

// Search one endpoint for the requested eligible occurrence. Not finding one
// is an ordinary result, not an error: `eligible` counts the matches seen and
// `unsupported` records a match skipped because replacing it would change the
// result type (a dependent position). Each caller decides what that means.
export function findRewrite(checker, root, carrier, rule, context, occurrence = 1,
  order = "preorder", deadline = performance.now() + 1000, work = null) {
  if (!Number.isSafeInteger(occurrence) || occurrence < 1) throw Error("Invalid rewrite occurrence.");
  if(work)work.traversals++;
  let visits = 0, candidates = 0, eligible = 0, unsupported = false;
  let found = null;
  const consider = (subject, path) => {
    if(++visits>512)throw new SearchLimit("Rewrite traversal budget exceeded.");
    for(const candidate of Array.isArray(rule)?rule:[rule]) {
      if(work)work.candidateVisits++;
      if (++candidates > 8192) throw new SearchLimit("Rewrite candidate budget exceeded.");
      if (performance.now() > deadline) throw new SearchTimeout("Rewrite elapsed-work budget exceeded.");
      if (candidates % 16 === 0) checker.kernel?.checkDeadline();
      try {
        const selected = candidate.instantiate?.(subject,deadline)
          ?? (candidate.instantiate ? null : candidate);
        if (!selected) continue;
        try { checker.check(subject, selected.carrier, context); }
        catch (error) { if (error.message === "Type mismatch.") continue; throw error; }
        if (!checker.equal(subject, selected.left, context)) continue;
        const hole = freshName("rewrite_hole",[root,selected.term],context,checker.dimensions);
        const variable = T.variable(hole);
        const contextTerm = T.lam(hole, selected.carrier, replacement(root, path, variable));
        try { checker.check(contextTerm, T.pi(hole, selected.carrier, carrier), context); }
        catch (error) {
          if (error.message !== "Type mismatch.") throw error;
          unsupported = true; continue;
        }
        eligible++;
        if(work)work.eligibleMatches++;
        if (eligible !== occurrence) continue;
        const after = replacement(root, path, selected.right);
        const dim = freshName("rewrite_dim",[root,selected.term,after],context,checker.dimensions);
        const raw = T.line(dim, carrier, T.app(contextTerm, T.at(selected.term, I.variable(dim))));
        const target = T.path(dim, carrier, root, after);
        const checked = checker.check(raw, target, context);
        found = {after, witness:checker.ascribe?.(checked,target)??checked,
          occurrence:eligible, visits,premiseRules:selected.premiseRules??[],rule:candidate};
        if(work)work.successfulRewrites++;
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
export function rewriteFirst(checker, root, carrier, rule, context, occurrence = 1,
  order = "preorder", deadline = performance.now() + 1000, work = null) {
  const {found, eligible, unsupported} = findRewrite(checker, root, carrier, rule, context,
    occurrence, order, deadline, work);
  if (found) return found;
  throw Error(unsupported ? "Rewrite match occurs in an unsupported dependent position."
    : `Rewrite occurrence ${occurrence} was not found (${eligible} eligible matches).`);
}
