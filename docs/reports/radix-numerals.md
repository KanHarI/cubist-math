# Numerals in the library

Step NT4 of the [archive retirement](../roadmaps/archive-retirement.md#number-theory-in-the-library),
2026-10-30. The archive's six `binary_*` modules (672 lines) are checked
against the library's binary naturals, NUM0 and NUM1's `bnat_*` modules,
and completed; its eleven `radix_*` modules (2,347 lines) are rebuilt over
binary `Nat` in four library modules (879 lines); and the Cubist tests and
JavaScript tests that imported the archive's numerals import the library's.
No archive module is deleted: that is NT5.

## The modules

Four modules, none of which uses an assumption; every declaration is
`computable`.

| Module | Holds |
| --- | --- |
| [`radix_numerals`](../../library/radix_numerals.cubist) | `Radix`, a natural number at least two, with `radix_two` and `radix_ten`; digits `Digit(r)`, which is `Fin(r.1)`, and nonzero leading digits; positive numerals `RadixPositive(r)`, a leading digit and then further digits, the last outermost, and `RadixNat(r)`, with zero separate; the value `radix_to_nat`, by Horner's rule in binary; the successor and its value law. |
| [`radix_operations`](../../library/radix_operations.cubist) | Addition, place by place with a carry, and multiplication, a digit at a time, where a numeral is multiplied by a digit through the digit's bits, doubling and adding in the radix; the value laws `radix_add_value` and `radix_mul_value`. |
| [`radix_conversion`](../../library/radix_conversion.cubist) | `nat_to_radix`, a number as that many times one, by its bits; uniqueness (`radix_injective`); the round trips; the equivalence `radix_equiv` and its Glue path `radix_path : Nat = RadixNat(r)`, along which transport converts both ways and binary addition and multiplication are the radix ones. |
| [`radix_factorials`](../../library/radix_factorials.cubist) | `radix_factorial`, one algorithm in every radix: the pair (k, k!) stepped n times by n's bits (`bnat_iterate`), counting and multiplying in the radix. Its value is n!; factorial equations carry along the path both ways; 10! in binary, carried to every radix, and computed digit by digit in base 10 and base 2 and carried back to binary. |

Three library modules gain laws the radix modules use, each stated in
general: `nat` right distributivity, `succ(a) * b = a * b + b` and the
interchange of sums (`nat_add_mul`, `nat_succ_mul`, `nat_add_interchange`);
`bnat_order_laws` equality from at most and not below, positive sums and
sums of strict bounds (`bnat_le_not_lt_equal`, `bnat_positive_add`,
`bnat_add_lt`); `bnat_division` the uniqueness of quotient and remainder
(`unat_division_unique`, `bnat_division_unique`).

### Design

- **The radix is a number, not a type of digits.** The archive's radix was
  `extra : UNat`, standing for `extra + 2`, and its digits a unary finite
  type, `RadixDigit(n) := Unit or RadixDigit(n - 1)`, ordered from the top so
  that increment was structural. Here a radix is `(b, evidence of 2 <= b)`
  and a digit a binary natural with its bound, so base ten is
  `radix_ten := (10, tt)` and its digit 8 is `(8, tt)`.
- **Uniqueness is division's.** A value `v * b + d` with `d < b` determines
  `v` and `d`, as quotient and remainder (`bnat_division_unique`); a leading
  digit is a value of quotient zero, so it is not the value of a longer
  numeral, whose quotient is positive. The archive proved the same division
  uniqueness inside its radix modules.
- **The value is the direct conversion to binary.** The archive had three
  representations, unary, binary and radix, and two conversions out of the
  radix. In the library binary `Nat` is the reference, so `radix_to_nat` is
  the archive's `radix_to_binary`, and the comparison with unary numbers is
  `bnat_unary`'s.
- **No unary counting.** The archive added a digit by that many successors
  (`radix_add_small`), multiplied by a digit by that many additions
  (`radix_add_copies`), read numbers in one successor at a time
  (`radix_of_nat`) and recursed on unary `n` for factorials. Here digits add
  with one comparison and at most one subtraction, a numeral is multiplied by
  a digit through the digit's bits, numbers are converted by their bits, and
  the factorial iterates by the bits of `n`.
- **Evidence from comparisons.** A computed digit's bound is the comparison
  `bnat_lt_decide`'s own evidence; the order laws, with their transports,
  only refute the branch that cannot happen, as in `bnat_order_laws`, so
  no transport is in what computes. A first version took a carried digit's
  bound by a transport.
- **The factorial iterates.** Defined by `nat`'s strong recursion, as
  `bnat_factorial` is, the radix factorial stopped with K344 at 30! in base
  10 in the REPL, where each level of that recursion returns under a
  transport (NT2's [report](binary-euclid.md#findings)). Iterating the pair
  (k, k!) by the bits of `n` has no transport, and computes 50!; its zero
  and successor equations follow from the value law and uniqueness.

## Correspondence

Each archive result and its library counterpart: **existing** in NUM0/NUM1,
**added** by NT4, **rebuilt** by NT4, or **superseded** where the archive's
statement concerns a unary object the library does not have. The library's
only unary number type is `UNat`, for structural recursion, and it has no
factorial: the archive's results relating the binary factorial to its unary
`factorial` (from `primes`) have no counterpart, and `nat`'s binary factorial
is the factorial.

### Binary numerals

| Archive | Library | |
| --- | --- | --- |
| `BinaryPositive`, `BinaryNat` (`binary_naturals`) | `BPositive`, `BNat` (`bnat`) | existing |
| `binary_positive_rec`, `binary_positive_cases` | `match` with structural recursion | existing |
| `binary_twice`, `binary_twice_succ` | `bnat_twice`, `bnat_twice_succ` | existing |
| `binary_digits`, `binary_literal`, notation `binary` | `bnat_digits`, `bnat_literal`, notation `bnat` (`bnat_notation`); `nat`'s notation reads the same literals, decimal included | existing |
| `binary_literal_digits`, `binary_literal_leading_zeroes` | `bnat_leading_zeroes` and the literals of [`binary_natural_foundation`](../../cubist-tests/binary_natural_foundation.cubist) | existing |
| `binary_positive_induction` (`binary_induction`, into `U0`) | `bpositive_induction` (`bnat_arithmetic`), in every universe | existing |
| `binary_positive_succ`, `binary_succ`, `binary_positive_add`, `binary_add`, `binary_positive_mul`, `binary_mul` (`binary_arithmetic`) | `bpositive_succ`, `bnat_succ`, `bpositive_add`, `bnat_add`, `bpositive_mul`, `bnat_mul` | existing |
| `binary_of_nat` | `bnat_of_unat` (`bnat_unary`) | existing |
| `binary_factorial(n : UNat)` | `factorial` (`nat`), `bnat_factorial` over binary `n` | existing |
| `binary_carry_example`, `binary_add_example`, `binary_mul_example` | `bnat_carry`, `bnat_add_bits`, `bnat_multiply_bits` ([`binary_natural_foundation`](../../cubist-tests/binary_natural_foundation.cubist)) | existing |
| `binary_factorial_step`, `binary_factorial_value_step`, `binary_factorial_zero` | `nat_factorial_succ`, `nat_factorial_zero` | existing |
| `binary_factorial_1` … `binary_factorial_ten`, a certificate a step | `nat_factorial_ten : factorial(10) = 3628800`, by computation (`radix_factorials`) | added |
| `binary_positive_to_nat`, `binary_to_nat` (`binary_equivalence`) | `bpositive_to_unat`, `bnat_to_unat` | existing |
| `binary_decode_one`, `binary_decode_even`, `binary_decode_odd` | by computation; `bpositive_decode_even`, `bpositive_decode_odd` | existing |
| `binary_decode_positive_succ`, `binary_decode_succ` | `bpositive_decode_succ`, `bnat_decode_succ` | existing |
| `binary_nat_roundtrip` | `bnat_unat_roundtrip` | existing |
| `binary_double`, `binary_double_succ`, `binary_encode_double` | `bnat_twice`, `bnat_twice_succ_step`, `bnat_encode_double` | existing |
| `binary_positive_roundtrip`, `binary_roundtrip` | `bpositive_roundtrip`, `bnat_roundtrip` | existing |
| `binary_nat_equiv`, `nat_binary_equiv`: `paths_`' `Equiv`, both ways | `unat_bnat_equiv`, a `ContrEquiv` from `UNat`, and its Glue path `unat_bnat_path` (`bnat_transport`), whose reverse transport is `bnat_to_unat` | existing |
| `nat_add_one`, `nat_double_add` (`binary_arithmetic_correct`) | `unat_add_comm`, `unat_add_interchange` | existing |
| `BinaryAddCorrect`, `binary_add_right_one`, the four digit cases, `binary_decode_add_even`, `binary_decode_add_odd`, `binary_decode_positive_add`, `binary_decode_add` | `BPositiveAddCorrect`, `bnat_add_right_one`, `bnat_add_even_even` …, `bnat_decode_add_even`, `bnat_decode_add_odd`, `bnat_decode_positive_add`, `bnat_decode_add` | existing |
| `BinaryMulCorrect`, `binary_mul_even`, `binary_mul_odd`, `binary_decode_positive_mul`, `binary_decode_mul` | `BPositiveMulCorrect`, `bnat_mul_even`, `bnat_mul_odd`, `bnat_decode_positive_mul`, `bnat_decode_mul` | existing |
| `binary_factorial_correct`: the binary factorial decodes to the unary one | — | superseded |
| `nat_3628800`, `factorial_ten_from_binary`: unary 10! is a decoded binary value | `nat_factorial_ten` | superseded |
| `number_equivalence_map` (`binary_univalence_transfer`) | an equivalence's map, `e.1` | existing |
| `univalence_transfer_equality`: an equation carried along `ua` by `UnivalenceBeta` | `glue_path_transport` (`univalence`); for factorials, `radix_factorial_from_nat` and `nat_factorial_from_radix`, which carry an equation along `radix_path` | added |
| `factorial_ten_via_univalence`: binary 10! carried to unary | `radix_factorial_ten`: binary 10! carried to every radix | added; superseded for unary |
| `binary_encode_factorial`, `binary_factorial_ten_via_nat`: unary 10! carried back to binary | `nat_factorial_ten_from_base_ten`, `nat_factorial_ten_from_base_two`: 10! carried from a radix back to binary | added; superseded for unary |
| — | `unat_bnat_add_operation`, `unat_bnat_mul_operation`: along the path, unary addition and multiplication are the binary ones | existing, beyond the archive |

### Radix numerals

| Archive | Library | |
| --- | --- | --- |
| `RadixDigit(n)`, `radix_digit_top`, `radix_digit_weaken`, `radix_digit_value` (`radix_naturals`) | `Digit(r) := Fin(r.1)`; a digit is its value with its bound, read by `.1` | rebuilt |
| `radix_digit_zero`, `radix_one` | `radix_digit_zero`, `radix_leading_one`, `radix_one` | rebuilt |
| `radix_digit_succ`: increment or overflow, structural | `bnat_lt_decide(succ(d.1), r.1)` in `radix_leading_succ`, `radix_append_succ` | rebuilt |
| the parameter `extra`, the radix `extra + 2` | `Radix`, with `radix_two`, `radix_ten` | rebuilt |
| `RadixPositive(extra)`, `radix_leading`, `radix_append`, `RadixNat(extra)`, `radix_zero`, `radix_positive` | `RadixPositive(r)`, `radix_leading`, `radix_append`, `RadixNat(r)`, `radix_zero`, `radix_positive`; the leading digit stores its value, nonzero, where the archive stored the value less one | rebuilt |
| `radix_positive_rec`, `radix_positive_cases`, `radix_positive_induction` (`radix_induction`) | `match` with structural recursion | existing |
| `RadixDigitStepLaw`, `radix_digit_lift_step`, `radix_digit_lift_law`, `radix_digit_succ_law`, `radix_digit_zero_value` (`radix_digit_laws`) | `radix_last_digit`: a digit whose successor is not below the radix is the last; the value laws below | rebuilt |
| `radix_positive_succ`, `radix_succ` (`radix_arithmetic`) | `radix_positive_succ`, `radix_succ` | rebuilt |
| `radix_add_small`: a digit added as that many successors | `radix_positive_add_digit`: one digit sum, with a carry | rebuilt |
| `radix_positive_add`, `radix_add` | `radix_positive_add`, `radix_add` | rebuilt |
| `radix_add_copies`: a digit times a numeral as that many additions | `radix_positive_scale`, `radix_positive_add_scale`: through the digit's bits | rebuilt |
| `radix_positive_mul`, `radix_mul` | `radix_positive_mul`, `radix_mul` | rebuilt |
| `radix_of_nat`: from unary, a successor at a time | `nat_to_radix`: from binary, by its bits (`radix_conversion`) | rebuilt |
| `radix_factorial(extra, n : UNat)`, `radix_factorial_step`, `radix_factorial_value_step`, `radix_factorial_zero` | `radix_factorial(r, n : Nat)`, `radix_factorial_succ`, `radix_factorial_zero` (`radix_factorials`) | rebuilt |
| `radix_positive_to_nat`, `radix_to_nat`: to unary (`radix_decode`) | `radix_positive_to_nat`, `radix_to_nat`: to binary `Nat` | rebuilt |
| `radix_decode_leading`, `radix_decode_append`, `radix_decode_one` | by computation | — |
| `radix_decode_shift_zero`, `radix_decode_shift_one` | not stated: for a variable radix and numeral they do not hold by computation alone, and follow from `nat_add_zero` and `nat_one_mul` | — |
| `RadixLeadingIncrement`, `RadixAppendIncrement`, `radix_decode_leading_increment`, `radix_decode_append_increment` | `radix_leading_succ_value`, `radix_append_succ_value`, `radix_carried_value` | rebuilt |
| `radix_decode_positive_succ`, `radix_decode_succ`, `radix_nat_roundtrip` | `radix_positive_succ_value`, `radix_succ_value`, `radix_nat_roundtrip` | rebuilt |
| `radix_nat_no_smaller_self`, `radix_nat_small_not_large`, `radix_eval_succ`, `radix_cancel_block`, `radix_division_zero`, `radix_division_successor`, `radix_division_unique` (`radix_uniqueness`) | `unat_division_unique`, `bnat_division_unique` (`bnat_division`) | rebuilt, in general |
| `radix_digit_bound` | `d.2`, the digit's own bound | — |
| `RadixDigitInjective`, `radix_digit_top_unique`, `radix_digit_lower_unique`, `radix_digit_injective` | `radix_digit_injective`, `radix_leading_digit_injective`, by `subtype_injective` | rebuilt |
| `radix_decode_positive`, `radix_nat_positive_decompose` (`radix_equivalence`) | `radix_positive_to_nat_positive`, on the bits | rebuilt |
| `radix_leading_not_append` | `radix_leading_not_append`, by division's uniqueness at quotient zero | rebuilt |
| `RadixPositiveInjectiveAt`, `radix_leading_injective`, `radix_append_append_injective`, `radix_append_injective`, `radix_positive_injective` | `radix_positive_injective` | rebuilt |
| `radix_decode_nonzero`, `radix_zero_injective`, `radix_nonzero_injective`, `radix_injective`, `radix_roundtrip` | `radix_injective`, `radix_roundtrip` | rebuilt |
| `radix_nat_equiv`, `nat_radix_equiv` | `radix_equiv`, from `Nat`, and its path `radix_path` | rebuilt |
| `radix_nat_distribute`, `radix_nat_add_cross` (`radix_arithmetic_correct`) | `nat_add_mul`, `nat_add_interchange`, `radix_place_add` | rebuilt |
| `radix_decode_add_small`, `RadixAddCorrect` and its cases, `radix_decode_positive_add`, `radix_decode_add` | `radix_positive_add_digit_value`, `radix_leading_sum_value`, `radix_append_sum_value`, `radix_positive_add_value`, `radix_add_value` | rebuilt |
| `radix_decode_add_copies`, `RadixMulCorrect` and its cases, `radix_decode_positive_mul`, `radix_decode_mul` | `radix_positive_scale_value`, `radix_positive_add_scale_value`, `radix_place_mul`, `radix_positive_mul_value`, `radix_mul_value` | rebuilt |
| `radix_factorial_correct`: to the unary factorial | `radix_factorial_value`: to the binary factorial | rebuilt |
| `radix_positive_to_binary`, `radix_to_binary` and their correctness (`radix_binary_equivalence`) | `radix_to_nat` itself | rebuilt |
| `binary_positive_to_radix`, `binary_to_radix`: doubling in the radix, and their correctness | `nat_to_radix`, the same doubling, and `radix_nat_roundtrip` | rebuilt |
| `binary_injective`, `radix_binary_roundtrip`, `binary_radix_roundtrip`, `radix_binary_equiv`, `binary_radix_equiv` | `radix_roundtrip`, `radix_nat_roundtrip`, `radix_equiv` | rebuilt |
| `radix_binary_leading_beta`, `radix_binary_append_beta`, `radix_binary_append_value`, `radix_binary_positive_beta`: certificates a digit at a time | — : conversions compute, as the contracts check | not needed |
| — | `nat_to_radix_succ`, `nat_to_radix_add`, `nat_to_radix_mul`, `radix_add_operation`, `radix_mul_operation` | added |
| `binary_to_radix_factorial`, `radix_to_binary_factorial` (`radix_univalence_transfer`) | `radix_factorial_nat` | rebuilt |
| `factorial_ten_binary_to_radix` | `radix_factorial_ten` (`radix_factorial_from_nat`) | rebuilt |
| `factorial_ten_radix_to_binary`, `factorial_ten_radix_to_nat` | `nat_factorial_from_radix` | rebuilt |
| `factorial_ten_from_base_ten`, `factorial_ten_from_base_two`, `factorial_ten_base_ten_to_binary`, `factorial_ten_base_two_to_binary` | `nat_factorial_ten_from_base_ten`, `nat_factorial_ten_from_base_two` | rebuilt |
| `factorial_ten_binary_to_base_ten`, `factorial_ten_binary_to_base_two` | `radix_factorial_ten(radix_ten)`, `radix_factorial_ten(radix_two)` | rebuilt |
| `converted_ten_*`, `converted_two_*`, `base_ten_3628800_to_binary`, `base_two_3628800_to_binary`: conversion a digit at a time | — : `radix_to_nat(radix_ten, radix_ten_3628800)` computes | not needed |
| `base_two_digit_*`, `base_two_leading_1`, `base_ten_digit_*`, `base_ten_leading_*` (`radix_factorial`) | digits written as values, `(8, tt)` | — |
| `base_two_factorial_value_1` … `_10`, `base_ten_factorial_value_1` … `_10`, a certificate a step | `radix_ten_3628800`, `radix_two_3628800`; `radix_factorial_ten_base_ten` and `radix_factorial_ten_base_two` by computation | rebuilt |

`radix_two_3628800` is `nat_to_radix(radix_two, 0b1101110101111100000000)`:
in base 2 the digits are the bits. The contracts write a base-2 factorial's
digits out (`radix.factorial_base_two`, 5!).

## Computation

[`radix_contracts`](../../tests/fixtures/contracts/radix_contracts.cubist)
states `expect_axioms([])` for the equivalence, uniqueness, the value laws,
the factorial's value and 10! in every radix, and evaluates: a carry through
two digits, a sum and a product with carries, a product with zero, 255 in
base 16, 3628800 to base 10 and back, 2^80 to base 10 and back, transport
along `radix_path` both ways, the transported binary multiplication, and the
factorial in base 10 (10!, and 30! read back), and in base 2 (5!, its digits
written out).

Limits, measured on this branch at `65888504` with `node cli/repl.mjs`:

| Entry | The kernel's queries (`evaluate !!…`, `evaluate … expecting`) | The REPL's value form |
| --- | --- | --- |
| `nat_to_radix(radix_ten, n)` and back | 2^80 (25 digits); 30 digits stop with K344 | 60 digits; 100 digits stop with E488 at the 20,000,000-cell budget |
| `radix_factorial(radix_ten, n)` | 35!; 40! and 50! stop with K344 | 60!; decoding it, `radix_to_nat(radix_ten, radix_factorial(radix_ten, 60))`, stops with E488 |
| `radix_factorial(r, 30)`, `r` 2 and 16 | computes | — |
| `factorial(n)`, `nat`'s binary factorial | 40! | 50! stops with K344 |

The kernel's limit is its syntax depth guard (K344: no term node deeper
than 512, `kernel/src/term_store.c`). Presumably a digit computed from
earlier digits is a term over theirs, so that each doubling in a
conversion, and each operation in a factorial, deepens the digits' terms. In the REPL the radix factorial computes past `nat`'s own,
whose strong recursion returns each level under a transport.

## Consumers

Moved to the library:

- [`wasm_binary_literal`](../../cubist-tests/wasm_binary_literal.cubist)
  checks `bnat`'s 27 declarations in WASM and refuses a false `0b`
  equation; [`wasm_bad_factorial`](../../cubist-tests/wasm_bad_factorial.cubist)
  refuses a false value of `nat`'s factorial;
  [`computability_evaluation`](../../cubist-tests/computability_evaluation.cubist)
  multiplies `bnat` literals, printed `bnat.(143)` where `unat` is
  selected, and imports `unat`, not `primes`. Their JavaScript tests
  (`tests/cubical-wasm.test.mjs`, `tests/computability.test.mjs`) follow,
  and the latter's parsing source imports `unat`.
- `tests/cubical-wasm.test.mjs` checks the arena of `radix_factorials`'
  10! computations in binary, base 2 and base 10, and of 10! carried from
  base 10 to binary; `tests/repl-session.test.mjs` evaluates `bnat_succ`
  under `nat`; the instruction driver's W-types test derives `bnat`.
- The language reference's binary numbers section and the quick reference
  show `bnat` and `nat`; the Cubist guide names the radix modules.

Left for NT5, which deletes the modules. NT5 did so on 2026-10-30; its row
in the [plan](../roadmaps/archive-retirement.md#number-theory-in-the-library)
records what became of each consumer.

- `tests/cubical-transfers.test.mjs`, with `tests/fixtures/factorial-transfer.cubist`
  and `tests/translator/number-transport.mjs`: it builds Glue transports of
  the archive's equivalences in JavaScript and checks that no transfer
  materializes the unary 3628800. `radix_conversion` and `radix_factorials`
  transport in Cubist, along `radix_path`.
- `tests/instruction-driver.test.mjs`: the face-search test derives
  `binary_univalence_transfer`'s `binary_factorial_ten_via_nat`, whose face
  unfolds to unary 10!, and the Glue test loads that module for the `ua`
  and `UnivalenceBeta` builtins.
- Printing the archive's `BinaryNat` as `0b` literals:
  `web/translator/numeral-printing.mjs`'s `binaryDigits`,
  `web/cubical-source-text.mjs`, and `tests/source-text.test.mjs`'s test of
  them.
- The archive catalog's titles (`web/proof-library.mjs`), the corpus test's
  comment on `binary_naturals`, the HoTT automation example's workload
  (`docs/examples/hott-automation/measure.mjs`, `baseline.json`), the
  tactical checkpoint [`binary-radix`](../tactical/binary-radix.md), and
  dated records: saved benchmark reports and the capture-bindings costs.
- `primes`' unary `factorial`, which only `binary_*` and `radix_*` use.

## Validation

See the NT4 row of the [plan](../roadmaps/archive-retirement.md#number-theory-in-the-library).
