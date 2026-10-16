# Follow-up reviewer evidence for PR #188 at `00d4ecce`

Reviewer report supplied by the repository owner on 2026-10-09, preserved
from `pr188-review-00d4ecce.md`. Results, mutation classifications and timings
below are the reviewer's observations at the named commits, not a new test
run by this documentation PR. The [gap inventory](frontend-generation-gaps.md)
records independent reproduction checks and the [roadmap](../roadmaps/frontend-generation.md)
assigns fixes and prevention work. Line numbers refer to the reviewed head.

## Review of `00d4ecce`

The review of `9c93220d` found six regressions, test gaps and shared items (a)–(e). All are fixed and tested, except a nested form of (b), described below. At this head the following pass: `npm test` (755/755), `build-site` + `test:site`, `test:browser`, `lint:cubist` and `git diff --check`. Each finding was compared with main (`cb525f07`, same kernel) and with `9c93220d`.

### Introduced by this PR (all in `00d4ecce`)

**1. A catch-all over a path constructor loses its endpoint diagnostic.**
```cubist
import hlevels;
inductive T : set U0 { t0; t1; seg : t0 = t1; }
def h(x : T) : T := match x { t0 => t0; _ => t1; };
```

- Main and `9c93220d` give E606 `found t1 = t1, expected t0 = t1`, located at the body.
- The PR gives E546 `Cannot generate seg: T must be a proposition; … Give checked h-level evidence, or an explicit obligation.`, located at the scrutinee `x`.
- With a `Nat` target (`first => zero; _ => succ(zero)`), it says `Nat is not a proposition: 0 and 1 differ`. Over an initial model, `match x { N.one => zero; _ => zero; }` says `Cannot generate N.one_mul`. Nothing was asked to be generated.
- Cause: `match.mjs:462` sends every failing implicit path clause to `automaticClause`, and reports that function's error. The comment and the PR description limit the route to recursive boundaries, but `seg` has no recursive argument.
- Fix: take this route only when the constructor has recursive positions. When `automaticClause` fails as well, keep the written body's mismatch.
- The test ("catch-all path clauses …") only asserts that some gap is named `bad`. Assert E606 and the endpoints.

**2. Law binders that inlining renames lose their links, and hover shows `c1`.**
```cubist
import hlevels;
theory T(U < UU0) { M : set U; c : M; op(x, y : M) : M;
  def k(x : M) : M := op(x, c);
  law l(c : M) : k(c) = op(c, c);
}
```

- The inliner now renames the law's `c` to `c1`, which is correct.
- The three uses of `c` now link under the name `c1`. Neither they nor the binder have a definition target.
- On main and `9c93220d`, all four linked to the binder at offset 112, named `c`.
- Cause: `sourceBinding` records the label `c` in `localSources` (`translate.mjs:164`), but the scope key stays `c1`. The alias filter `source?.name===name` (`translate.mjs:119`) then drops the alias, and `recordReferences` (`cubical-program.mjs:124`) finds no source. The renamed uses carry no label either.
- Mutants that drop the label at `translate.mjs:165` or at `scope.fresh` (`:609`) survive the suite, so no test checks this.

**3. E871 has a zero-width location (minor).**

- `law l(n : Nat) : (match n return M { zero => c; succ(c) => k(c); }) = c;` reports E871 at 5:3 with an empty span.
- `theories.mjs:175` locates the error at the whole law type. It should point at the pattern binder or the helper call.

### Shared with main (for the TODO)

**(a) A derived operation's parameter captures an inlined helper's field. This silently changes meaning.**
```cubist
import hlevels;
theory T(U < UU0) { M : set U; c : M; op(x, y : M) : M;
  def k(x : M) : M := op(x, c);
  def kk(c : M) : M := k(c);
}
def captured(S : T(U0), x : S.M) : S.kk(x) = S.op(x, x) := refl(S.op(x, x));
```

- `captured` checks on main, `9c93220d` and the PR, so `kk(x)` is `op(x, x)` rather than `op(x, c)`. Laws over `kk` inherit the wrong meaning.
- Cause: `theories.mjs:539` inlines `process(item.value)` without the operation's parameters as binders, so the substitution sees no binder to rename apart.
- `pr-188-todo.md:41` checks off "caller binders capturing inlined helper fields", and `syntax-hygiene.md:44` states that invariant without restriction. Both hold for laws and child theories but not for derived operations. Qualify both when recording this.

**(b) A derived operation that calls a recursive one is refused with a message about field types.**

- With a recursive `iter`, `def twice(n : Nat) : M := op(iter(n));` gives E845 `iter is recursive, and a field's type cannot unfold it` on both.
- The span is empty, and `twice` is not a field.

### Test gaps

- Mutation run: 20 mutants of `00d4ecce`'s changes, against the theory, scope, match and corpus tests. 13 were killed, one was skipped, and six survived:
  - The two label mutants: covered by finding 2.
  - `notationScope` aliases (`translate.mjs:1115`). Neither the last review's `n > 0` source nor plain numerals distinguish this mutant any more, because capture now marks both. The scope that `initial-models.mjs:46` builds may be dead: test it or remove it.
  - The branch-level `RECURSIVE` update (`match.mjs:365`), the `recursiveCall` source check, and re-adding `IsSet`/`IsProp` to the globals. No source distinguishes them; they look equivalent or defensive.
- The `explicit head` guard (`patterns.mjs:196`) also survives, but top-level explicit path clauses never reach it, and `p(y) @ i => tt` stays refused.

### Checked without findings

- An inherited helper under a child's law binder: main captures it; the PR reads it correctly.
- Bare and partial helper uses in laws now check with the right meaning (main: E343).
- E871 does not fire for a pattern binder that does not enclose the helper use.
- Recursive derived operations:
  - inherited by a child;
  - reached as `N.model.iter` on an initial model;
  - with a pattern binder named after the operation, which gives the correct shadowing error (E352).
- Explicit path clauses keep their bodies: `p(y) @ i => k(y)` checks.
- Ordinary inductives under `use`: opened fields now shadow later globals, as they do in defs.
  - This changes the meaning of existing code: after `use multiplicative;` and `inductive M`, the constructor argument in `inductive Box : U0 { box(n : M); }` now reads `multiplicative.M`.
  - No corpus source is affected.
- Timing: checking `import hlevels; import algebra;` takes a median of 1.32 s on main and 1.41 s on the PR (seven interleaved runs). This is within the 5–9% the TODO records.

Note: the main checkout has an untracked `docs/reports/pr-188-todo.md`, the `68f1bf35` version. #188 now tracks that path, so after it merges, pulling main will refuse to overwrite the file.
