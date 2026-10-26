# PR #318: display follow-up

Found while fixing #318's second review (numeral abbreviations that did not
read back in the scope they print for). #318 checks numerals and literals:
the printer prints `n` bare only where the selected notation reads it, by
name and identity, and `name.(n)` only where `name` selects that notation in
the printing scope (`notationForScope` in
`web/translator/notation-context.mjs`, which resolves names as
`selected` in `web/translator/theories.mjs` does, through the scope's
lexical context where it has one). The printer applies that check in
`selects`, `qualifies` and `readBack` at the top of `sourceText`
(`web/cubical-source-text.mjs`). The items below are outside numerals and
remain unfixed; each reproduces on main.

- [ ] An operator prints in its notation's spelling by the notation's name
  alone. With `import nat; def sum_(x : Nat) : nat.(x + 3) = nat.(x + 3) := refl(nat.(x + 3));`
  followed by `notation nat { x + y := mul(x, y); }`, `print(typeof(sum_))`
  shows `forall x : Nat. nat.(x + 3) = nat.(x + 3)`, which reads back as a
  product. The infix branch of `sourceText` (`printing?.operator`) could take
  the same `selects`/`qualifies` check and otherwise print the call.

- [ ] A model's operator prints bare where a notation of the model's name is
  selected, without checking that the term's model is the selected one. With
  `def ring_copy : CommRing(U0) := …; use ring_copy;` and
  `def doubled(ring_copy : CommRing(U0), x : ring_copy.R) : ring_copy.(x + x) = ring_copy.(x + x) := …`,
  `print(typeof(doubled))` shows `forall ring_copy : CommRing(U0). forall x : ring_copy.R. x + x = x + x`,
  whose `+` reads through the selected global model. The projection branch
  compares `selection === show(model)`; the selection's receiver, which
  `notationForScope` now gives as `selectionReceiver`, would tell them apart.

- [ ] A constructor prints by its name, which an opened model's field can
  shadow. After `use ring_copy;` for a ring of differences, `zero` is the
  ring's field, so a unary value printed as `succ(succ(zero))` (as #318
  prints one where `unat` no longer selects unat's notation) reads back
  against the field. Name shadowing of displayed constructors and
  definitions belongs to display naming (`forSource` in
  `web/display-naming.mjs`), which marks a name qualified only for a
  dimension of the same spelling.

- [ ] A context that `notationForScope` did not build carries no scope
  lookup, and the printer then trusts a notation's name, as it did before
  #318: the file-level context a declaration's messages print in before its
  item scope (`{selection: selectionName(d.uses), selectionIdentity: null}`
  in `web/translator/translate.mjs`) and hand-built contexts in tests.
