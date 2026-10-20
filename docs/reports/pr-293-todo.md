# PR #293: static-site validation follow-up

Found while validating nondependent quotient descent on main `eb1524a2`
plus PR #293. This is outside the quotient change and remains unfixed here.

- [ ] `tests/site.browser.mjs:117` forks the first example under `#values`
  on `reference/types.html`, then waits for `seven : UNat`. The first
  example now defines `wide`; the example defining `seven` is second.
  Both the selector and example order are already present on main. Select
  the example by its source or a stable identity and rerun the complete
  static-site test. The observed run timed out at that wait after 180s;
  Euclid, F4, reference checking and excerpts passed before it, but later
  scenarios were not reached. PR CI does not run this static-site script;
  its full JavaScript suite separately checks reference examples.
