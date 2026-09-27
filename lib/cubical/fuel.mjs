// Deterministic fuel for proof search (docs/roadmaps/hott-automation-roadmap.md,
// A4; work plan L1.3). A tactic's search — matching, traversal, premise search
// and the kernel queries they ask — spends counted fuel, never elapsed time, so
// the same source succeeds or fails the same way on any machine and in any
// session.
//
// Each tactic search (rw's search for one rule, a simplification, simpa's two)
// has its own fuel, and a declaration's elaboration has one around them all.
// What a search counts:
//   visits      subterms the rewrite traversal considers
//   candidates  rules tried at those subterms, failed ones included
//   rewrites    rewrites made, premise searches' included
//   premises    premise searches started; a remembered outcome is free
//   nodes       term nodes the search's bookkeeping walks: rule patterns and
//               the keys of the goals it has seen
//   queries     kernel queries asked: inferences, checks, weak heads and
//               equalities, failed ones included
// A search's spending also counts toward its declaration's, whose limit is on
// queries alone: that bounds everything a declaration asks the kernel,
// rebuilding proofs after their searches included.
//
// Cache and reset accounting. Fuel starts from zero at each search and each
// declaration, and counts questions, never the kernel's steps: the kernel's
// caches answer a question cheaply in a session that has met it before, so
// its steps differ between a fresh session and a reused one, while the
// questions asked, and so the fuel, do not. The search's own caches, such as
// remembered premise outcomes, belong to that search. Each question's work
// is bounded instead by the kernel's step budget per operation, and running
// out of it is reported as the kernel's, not as fuel. A declaration deadline,
// when one is set, is only a safety timeout, reported as such.
// Defaults, from the baseline in tests/fixtures/search-fuel.json
// (tools/search-fuel-baseline.mjs): four times the most any search of the
// archive, the rebuilt library, the example fixtures and the checked
// reference examples spent, rounded up; for premise searches and rewrites,
// at least four times the bound one simplification already has, so that
// bound still decides.
export const SEARCH_FUEL = Object.freeze({
  visits: 10000, candidates: 10000, rewrites: 500, premises: 500, nodes: 100000, queries: 50000,
});
export const DECLARATION_FUEL = Object.freeze({ queries: 50000 });

const nouns = { visits: "subterm visits", candidates: "candidate rules tried", rewrites: "rewrites",
  premises: "premise searches", nodes: "term nodes walked", queries: "kernel queries" };
const count = n => n.toLocaleString("en-US");

// Out of fuel. Its `kind` is "fuel", as a checker rejection's is "mismatch",
// "budget" or "deadline", so a caller can tell the three kinds of limit apart.
// A search out of fuel stops as a whole: premise search does not contain it.
export class SearchFuelExhausted extends Error {
  constructor(search, fuel, limit) {
    super(`${search} ran out of search fuel: ${count(limit)} ${nouns[fuel]}.`);
    Object.assign(this, { kind: "fuel", fuel, limit, search });
  }
}

export class SearchFuel {
  // `search` names the search in messages; `record(used)` hears what it
  // spent when it closes. Spending also counts toward `parent`. A
  // declaration's fuel is marked, as searches run inside it.
  constructor(search, limits = SEARCH_FUEL, { parent = null, record = null, declaration = false } = {}) {
    this.search = search;
    this.limits = limits;
    this.parent = parent;
    this.record = record;
    this.declaration = declaration;
    this.used = Object.fromEntries(Object.keys(nouns).map(kind => [kind, 0]));
    this.open = true;
  }
  spend(kind, amount = 1) {
    // A closed search's scopes can still be used, to rebuild its proof: that
    // work is its declaration's.
    if (this.open) {
      const used = this.used[kind] += amount, limit = this.limits[kind] ?? Infinity;
      if (used > limit) throw new SearchFuelExhausted(this.search, kind, limit);
    }
    this.parent?.spend(kind, amount);
  }
  close() {
    if (!this.open) return;
    this.open = false;
    this.record?.(this.used);
  }
}

// What a declaration's searches spent: how many ran, and the most any one
// spent of each kind.
export const emptySearchRecord = () => ({ searches: 0, most: Object.fromEntries(Object.keys(nouns).map(kind => [kind, 0])) });
export function recordSearch(record, used) {
  record.searches++;
  for (const kind of Object.keys(used)) record.most[kind] = Math.max(record.most[kind], used[kind]);
}
