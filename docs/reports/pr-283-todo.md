# PR #283: literal readers follow-up

Found by #283's final review. The behavior is shared with main's literal
readers, so it is recorded here and not changed in #283 alone.

- [ ] An underscore is skipped wherever it follows a literal's first digit,
  so malformed separators are accepted rather than refused with E905.
  `1__2` reads as 12, and `1_`, `1.2_` and `1/1__2` are accepted.
  - #283's `bq_integer_digits` and `bq_decimal_digits` skip any underscore.
    A denominator inherits the same rule from `bnat_literal`
    (`bnat_decimal_digits` in `library/bnat_notation.cubist`).
  - Main at `8beac486` reads `bnat.(1__2)` as 12 and `bnat.(1_)` as 1.
    `leading_digits` in `library/lexemes.cubist`, which `rationals` uses,
    skips every underscore too ("_ between them ignored").
  - A fix makes every reader take an underscore only between two digits:
    `bnat_notation`, `lexemes`' `leading_digits`, `rationals` and
    `binary_rationals` together. It adds refusal contracts with their
    positions, as #283's `*_position` contracts assert them.
