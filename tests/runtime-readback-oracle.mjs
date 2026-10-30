// The readback oracles of docs/roadmaps/runtime/typed-readback.md (W1),
// run on the value forms a program computes in the runtime: each print
// whose value form the runtime computed (valueFormOf in
// web/translator/translate.mjs) is read back before its query is disposed
// of, inside its declaration, where the query's handles are the kernel's.
//   - By value, with origins off: the full normal form of R(root) is the
//     kernel's full normal form of the evaluated term (3.6, claim 3).
//   - Observed heads: each head an observation returned after η, read back,
//     has the full normal form of the cell it was asked of.
// The value form is computed by a query made for readback, which keeps
// those heads and its type values' bindings, and otherwise is the one the
// runtime would make.
//   - By origin: a query made with origins walks the same value form, and
//     the folded normal form of its R(root) is the kernel's folded normal
//     form of the term (3.4's target).
//   - Typing: where R(root) is small, the instruction driver checks it at
//     the term's type (claim 1).
// Equality is syntax only (alphaEqual), never conversion. The two normal
// forms and their comparison get a fixed budget each, and a comparison
// whose normal forms do not complete, past that budget ("budget") or past
// the kernel's syntax depth (K344, "deep"), is counted, not decided.
import { Translator } from "../web/translator/translate.mjs";
import { valueForm } from "../web/translator/evaluation.mjs";
import { RuntimeQuery } from "../web/cubical-runtime.mjs";
import { InstructionDriver } from "../web/cubical-instruction-driver.mjs";
import { KernelError } from "../web/cubical-kernel.mjs";

const deep = error => error instanceof KernelError && error.message === "Native prototype syntax depth exceeds 512.";
// Kernel queries with a fixed step budget each: their result, or null when
// a budget ran out.
export function within(kernel, steps, query) {
  const { stepBudget, maxQuerySteps } = kernel, fixed = BigInt(steps);
  Object.assign(kernel, { stepBudget: fixed, maxQuerySteps: fixed });
  kernel.setStepBudget(fixed);
  try { return query(); }
  catch (error) { if (error instanceof KernelError && error.kind === "budget") return null; throw error; }
  finally { Object.assign(kernel, { stepBudget, maxQuerySteps }); kernel.setStepBudget(stepBudget); }
}

// The nodes of a term as a tree, counted up to a bound.
export function treeSize(kernel, handle, bound = Infinity) {
  const sizes = new Map(), pending = [handle];
  while (pending.length) {
    const id = pending.at(-1), node = kernel.node(id), missing = node.children.filter(child => child && !sizes.has(child));
    if (missing.length) { pending.push(...missing); continue; }
    pending.pop();
    sizes.set(id, Math.min(bound, 1 + node.children.reduce((sum, child) => sum + (child ? sizes.get(child) : 0), 0)));
  }
  return sizes.get(handle);
}

// What a readback failure was: a Lift refused, a readback past the
// kernel's syntax depth (K344), or anything else, a defect.
const failure = error => error?.kind === "unsupported" ? { refused: error.message }
  : deep(error) ? { deep: error.message } : { error: `${error.kind ?? error.name}: ${error.message}` };

// The outcomes some oracle contradicts, or whose readback failed: each
// oracle must agree or leave its normal forms undecided, and a readback
// typed must type.
export const disagreements = outcomes => outcomes.filter(outcome => ![outcome.value, outcome.heads, outcome.folded]
  .every(verdict => verdict === true || verdict === "budget" || verdict === "deep") || outcome.typed !== undefined && outcome.typed !== true);

// Watch the value forms of the program checks made until `restore()`.
// Each one the runtime computes adds an outcome to `outcomes`: its source,
// and for each oracle true (agreed), false (differed), "budget" or "deep"
// (undecided), or the readback's failure; the heads' undecided comparisons
// are counted apart (`undecidedHeads`). `typing` is the largest tree size
// of R(root) typed. The value form is computed by a query of class `Query`,
// made for readback where the runtime would make one.
export function watchReadbacks({ steps = 2000000, typing = 0, Query = RuntimeQuery } = {}) {
  const outcomes = [], valueFormOf = Translator.prototype.valueFormOf;
  Translator.prototype.valueFormOf = function (result, scope, node, kernel) {
    const checker = this.checker, made = checker.runtimeQuery;
    let query = null;
    const observed = [];
    checker.runtimeQuery = judgement => {
      const asked = made.call(checker, judgement);
      if (!asked) return null;
      asked.dispose();
      query = new Query(checker.kernel, judgement, { ...checker.runtimeLimits(), readback: true });
      const observeNow = query.observeNow;
      query.observeNow = (handle, options) => { observed.push(handle); return observeNow.call(query, handle, options); };
      query.dispose = () => {};
      return query;
    };
    try {
      const value = valueFormOf.call(this, result, scope, node, kernel);
      if (query && this.valueFormRecord.by === "runtime") {
        // The oracles' queries are no demand of the program's: they run past
        // any recording of its queries on the kernel instance, as
        // tests/evaluation-demand-marks.test.mjs records them.
        const instance = checker.kernel, recorded = ["head", "normalize", "normalizeFolded"].filter(name => Object.hasOwn(instance, name));
        const recording = recorded.map(name => [name, instance[name]]);
        for (const name of recorded) delete instance[name];
        try {
          outcomes.push({ source: scope.unit.source.slice(node.start, node.end).trim(),
            ...oracles(this, checker, Query, query, observed, result, node, kernel, steps, typing) });
        } finally { Object.assign(instance, Object.fromEntries(recording)); }
      }
      return value;
    } finally {
      delete checker.runtimeQuery;
      if (query) Query.prototype.dispose.call(query);
    }
  };
  return { outcomes, restore() { Translator.prototype.valueFormOf = valueFormOf; } };
}

function oracles(translator, checker, Query, query, observed, result, node, at, steps, typing) {
  const kernel = checker.kernel, term = result.expression, outcome = {};
  // The two normal forms and their comparison, itself a budgeted query.
  const same = (normalize, a, b) => {
    try {
      const verdict = within(kernel, steps, () => ({ equal: kernel.alphaEqual(kernel[normalize](a), kernel[normalize](b)) }));
      return verdict ? verdict.equal : "budget";
    } catch (error) { if (deep(error)) return "deep"; throw error; }
  };
  let root;
  try {
    root = query.readback();
    outcome.value = same("normalize", root, term);
  } catch (error) { outcome.value = failure(error); }
  // Every observed head is compared: a disagreement fails the oracle
  // whatever came before it, and an undecided comparison is counted.
  try {
    outcome.heads = true;
    for (const handle of observed) {
      const agreed = same("normalize", query.readback(handle, { head: true }), query.readback(handle));
      if (agreed === false) outcome.heads = false;
      else if (agreed !== true) {
        outcome.undecidedHeads = (outcome.undecidedHeads ?? 0) + 1;
        if (outcome.heads === true) outcome.heads = agreed;
      }
    }
  } catch (error) { outcome.heads = failure(error); }
  if (typing && typeof root === "number" && treeSize(kernel, root, typing + 1) <= typing) {
    try { new InstructionDriver(kernel).check(root, result.typeHandle); outcome.typed = true; }
    catch (error) { outcome.typed = failure(error); }
  }
  // The same value form, walked by a query that keeps origins.
  const folded = new Query(kernel, result.judgement, { ...checker.runtimeLimits(), origins: true });
  try {
    valueForm(folded.root, Translator.prototype.runtimeQueries.call(translator, { spend() {} }, folded, at), node);
    outcome.folded = same("normalizeFolded", folded.readback(folded.root, { origins: true }), term);
  } catch (error) { outcome.folded = failure(error); }
  finally { folded.dispose(); }
  return outcome;
}
