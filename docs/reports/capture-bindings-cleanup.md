# Cleanup after CB0–CB7

Status: complete in #241, separately stacked on #240. Claude round 2 is clean
at `1481d352`; final documentation only records completion.

The audit follows the recurring review root: obsolete producers and descriptive
state should disappear once their responsibilities have moved. It found two
remaining cases after CB7, not a reason for a new general abstraction.

- Every semantic contract now requires its desired result. Both old defect maps
  are empty, but strict/fixed/known-defect classification and a historical
  observation transformer still surround those assertions. Replace that staging
  protocol with direct assertions. Preserve fixture-precondition classification,
  independent intended/captured clients, and bounded shrinking that compares each
  candidate against its own desired result and preserves the structural difference.
- Helper cycle validation constructs an unused pending list, and expanded-signature
  analysis returns a wrapper whose sole production consumer reads one recursive
  dependency. Remove those unused summaries. Keep the existing complete expansion
  and dependency walk, unresolved alternatives, diagnostic origins, and separate
  checking/analysis types used by admission and support planning.

The audit also checked scope/replay ownership, inert snapshots, binding receipts,
slot decisions and generated-artifact views. These preserve distinct tested
contracts; collapsing them would lose behavior. Historical cost and mutation
reports remain unchanged. Empty staging maps can be removed while the original
CB0 observations remain linked to their exact historical revision.

Four tests of the retired staging protocol are removed. The two meaningful
shrinker controls remain, as do all product positive/negative witnesses and
observation-fault tests. At `e5cf519f`, all 117 focused tests, 1,328 full-suite
tests, 3,857 corpus checks and twelve mutation contracts pass (terminal exit 0).
The suite has zero skips/TODOs; the four-test reduction is exactly the retired
staging protocol.

Claude round 1 confirms production equivalence and the harness boundaries, but
finds that the rewritten shrinker control lost its distinguishing incorrect
result. This repeats the obsolete-producer root in reverse: removing the old
observation transformer also removed the control's second kind of failure.
The abstraction still compares structural differences correctly. Restore that
negative case directly in the existing fixture, with a different refused client,
so accepting any failure instead of the same failure breaks the control. Do not
restore staging modes or add another test framework. Remove the redundant
post-validation deferred assertion already covered by the same test's earlier
reference check. Production code and semantic witnesses remain unchanged.

The corrected two-line fixture passes all six affected shrinker/dependency tests.
A temporary copy with the predicate weakened to accept any failure now fails
with `ERR_ASSERTION` at the inheritance-preservation check; the unchanged
candidate-error control still passes. Claude round 2 is clean at `1481d352`.
Its independent probe also rejects comparisons based only on difference count
or values without paths, and its focused run passes all six tests. No production,
semantic-harness or source-witness changes followed the full gate. Review stops
clean after two rounds, with no new modes, helpers or frameworks.
