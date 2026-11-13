# PR #355: decoding speed follow-up

Found while reviewing #355's third round. It also occurs on main `e5c50082`
(#354), outside the speed change, and remains unfixed here: #355 keeps
#354's behaviour exactly. It belongs to the display-names follow-up, which
reworks the same code.

- [ ] The display's renaming of made-up names (`SourceNames`,
  `web/cubical-elaborator.mjs`) depends on what was shown before. The same
  term shows differently in a fresh session and in one that showed it
  earlier.
  - **Fresh session:**
    1. A fresh entry `y`, spelled `y'1`.
    2. A fresh entry `x`, spelled `x'1`.
    3. `λ (x'1 : Unit). x'1` shown: `fun (x : Unit) => x`.
  - **Shown before:**
    1. A fresh entry `y`, spelled `y'1`.
    2. The λ encoded, settled, and shown in a declaration that is rolled
       back: `fun (x' : Unit) => x'`.
    3. A fresh entry `x`, spelled `x'1`.
    4. The λ shown again: `fun (x' : Unit) => x'`.
  - Both sessions end with the same stems (`y'1` → `y`, `x'1` → `x`).
  - **Mechanism:**
    - `SourceNames.apply` memoizes per decoded object (`results`). It reads
      the stems as they stand (`this.stems.get(value.name)`).
    - Variants made later add stems or overwrite them: `shownBinderName`
      and `EntryNames.spelling`, in `web/cubical-variables.mjs`.
    - The λ's decoding is the same object across the rollback, so the result
      made before `x'1` was a variant is served after.
  - **Constraint on the fix:** routing `SourceNames` through the decoder's
    fixed stems (`EntryNames.stemOf`) changed which path proof search took in
    `CommRing.ring` and `Field.comm_ring` (6 more kernel instructions each),
    with outputs unchanged. So the display's names reach elaboration
    somewhere, and a fix must be checked by a differential run that
    compares kernel work, not outputs alone.
