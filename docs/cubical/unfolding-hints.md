# Selective unfolding experiment

`cc_kernel_set_unfolding_hints(kernel, references, count)` selects checked
reference handles for a preliminary conversion pass. It is a reduction strategy,
not a proof rule. It introduces no assumptions and never approves an equality
without comparing its terms. Count zero clears the selection. A scoped caller
must clear it in a `finally` block, including after a failed check. Hints apply
to both checking and closed definition registration.

The preliminary pass compares terms structurally while unfolding only selected
definition heads. Explicit lambda applications, projections of exposed pairs,
and checked path endpoints can compute. Unselected definitions stay folded.
If this pass cannot establish equality, the existing converter runs normally.
The selection is an allowlist for the first pass, not an ordered list; order of
entries has no mathematical or operational significance. The default converter
is unchanged when no hints are installed.

The public setter validates definition references, rejects zero/out-of-range or
nondefinition handles, ignores duplicates, and preserves the previous selection
if a new list is invalid. Like all native term handles, reference integers belong
to one kernel arena. Passing a same-valued integer from another arena cannot be
detected separately from the local handle it aliases; the browser must maintain
its existing handle ownership discipline. Hints cannot make such an integer into
a proof certificate.

## Structure path roundtrip

The captured `structured_sets.structure_path_roundtrip` judgment previously
exhausted the native 10,000,000-step checking/reduction budget. The large
contraction proof was being unfolded merely to compare two presentations of its
arguments. These seven aliases are sufficient to expose the common computation:

```text
field_logic__field_first
identity_systems__identity_total_point
identity_systems__identity_system_decode
structured_sets__structure_iso_point
structured_sets__structure_iso_center
structured_sets__structure_equality_iso
structured_sets__structure_iso_equality
```

With the selection, the identical open judgment takes **12,683 reduction steps**
and **300 checking steps**, with **302,989 total arena nodes** including the 228
previously checked definitions and input syntax. Its final closed definition also
checks with the same selection. `identity_system_encode` and the structure's
contraction remain folded during the successful comparison. No operation budget
was increased.

An earlier shared-head comparison experiment did not solve the fixture by itself
and was removed. The retained change is the explicit selective pass and its
existing-converter fallback.

`fixtures/structure-path-roundtrip.json.gz` is the exact native-checking fixture,
compressed deterministically. It contains inert terms, expected type, earlier
checked definitions, and the original explicit assumption context; it contains
no cached approval or old-kernel certificate. The test rechecks every preceding
definition, checks the open judgment, and registers a closed abstraction of that
judgment. `tests/unfolding-hints.test.mjs` additionally rejects false endpoints
under several selections. `c/tests/test_unfolding_hints.c` covers API validation,
transactional replacement, clearing after failure, and false-path rejection.

The native test protocol accepts `H count reference-alias...`; `native.mjs`
exposes `unfoldingHints` on a final query and on individual definition entries.
The MathScript expression `with unfolding [alias, ...] { expression }`
scopes these hints in the frontend. A checked helper can retain the selected
strategy for replay without leaking it into surrounding expressions. The
parser node is `withUnfolding`, with name-token `hints` and an expression `body`.
