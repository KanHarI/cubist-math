# Evaluation demand marks: acceptance report (DM5)

Measured on 2026-10-23 with [`report.mjs`](report.mjs). The marks are
measured on the branch of this report, on top of
[#305](https://github.com/KanHarI/cubist-math/pull/305) and
[#304](https://github.com/KanHarI/cubist-math/pull/304) (`58247de6`). The
comparison is main at `8f66420c`. Both have kernel sources `ee8b2f32`: the
marks change no kernel code.

Each case runs in a fresh checked program, through the REPL as the CLI runs it
(`web/repl-session.mjs`). The case's setup runs first, then its entry with a
fixed budget of 100M query ticks. For each entry the script records:

- the first result's text, its length and its SHA-256;
- the query ticks and queries the entry alone spent;
- how many times it normalized a term, and how many of those failed.

For the last normalization it also records that normalization's own ticks.
If that normalization failed, it records the failure; otherwise it records
the distinct objects of the normal form's decoding (arrays among them), and
its digest.

The digest is `sharedNormalDigest` of the normal form's decoding, from
`tools/evaluation-baseline.mjs`. It compares terms exactly as that file's
`normalDigest` does, up to the names of bound variables and dimensions.
Unlike `normalDigest`, it reads each object the decoding shares once for
each way its free names are bound: unshared, these normal forms are too large
to walk. `tests/evaluation-demand-marks.test.mjs` checks that the two agree.
It covers every one-part change to the decoding of terms of every kind. It
also covers each of those terms met again beneath every context of up to two
binders, of either kind, of each name the term holds. In those contexts, the
tests check that sharing changes no digest. They also cover terms that share
parts under different binders, and terms alike but for their binders' names
and slots.

Repeated runs give identical counters. With `--root=CHECKOUT`, the script
measures another checkout, here main, with the spelling each case had before
the marks: `expecting _` for `expecting !!_`. A case main cannot spell is
measured on the branch only.

The counters are not the
[note's measurements](../evaluation-demand-marks.md#measurements). Those came
from [`probe.mjs`](probe.mjs), which queries the kernel on definitions checked
in one module, in a different program state. Every comparison below is made
the same way on both sides.

## Results

| Case | Entry on the branch | Branch | Main |
| --- | --- | --- | --- |
| Value form | `evaluate small_inverse;` | `class((class((3, 0)), class((2, 0)), <fun>))`, 28,085 ticks, 13 queries, no normalization | the full normal form, 71,027,452 ticks |
| Normal form | `evaluate small_inverse expecting !!_;` | 71,027,452 ticks, 1 query; 2,898,283 objects, digest `e3862859aa604076` | the same: ticks, queries, objects, digest and text |
| Lazy pattern | `evaluate euclid(3) expecting (7, _);` | `(7, <unevaluated>)`, 149,523 ticks, 4 queries | 223,521 ticks, the whole value normalized (1,971 objects) |
| Weak head | `evaluate !euclid(4);` | the pair, its components as they are, 133 ticks, 1 query | — |
| Prime of `euclid(4)` | `evaluate euclid(4) expecting (5, _);` | `K344` normalizing the first component, after 651,994 of the entry's 652,154 ticks | `K344` normalizing the whole value, 662,737 ticks |
| Bare hole | `evaluate euclid(3) expecting _;` | refused with `E485`, no query | accepted: 223,501 ticks, the whole value normalized |
| Eta | `print(evaluate(!(fun (n : UNat) => succ(n))));` | `succ`, 3 ticks | — |
| `rationals.(2/3)` | `… expecting !!_;` | 71,001,788 ticks, 158 queries; 2,853,781 objects, `8dff0fb0f91b2a9c` | the same |
| `rationals.(0.5)` | `… expecting !!_;` | 72,209,323 ticks, 158 queries; 2,855,531 objects, `376ba440da51ef3e` | the same |
| `integers.additive_` | `… expecting !!_;` | 73,120,014 ticks, 7 queries; 3,061,849 objects, `71f8a824cff38363` | the same |

The rational cases run in the debugging plan's main-only reproduction,
[`probe-sources.mjs`](probe-sources.mjs)'s `rational`. The Euclid cases import
`euclid`. The literal and theory cases import `rationals` and `integers`.

### Against the acceptance list

The [acceptance list](../evaluation-demand-marks.md#acceptance-for-the-implementation)
holds as follows.

- **Small inverse, value form.** The REPL prints the numerator and the
  denominator, with the nonzero certificate suspended as `<fun>`, in 28,085
  ticks. The bound is 100,000, and the probe's walk was 27,918. The second
  half of the item, `evaluate bq_inv(-2/3);` printing `-3/2`, waits for
  [#283](https://github.com/KanHarI/cubist-math/pull/283), still open.
- **Engine gate.** `expecting !!_` reproduces main exactly. The entry's ticks
  and queries, the normal form's ticks, its objects, its digest and the text
  shown are all the same.
- **Euclid.**
  - `euclid(3)` against `(7, _)` normalizes only the first component and the
    expected `7`, never the certificate. It costs 149,523 ticks where main
    normalizes the whole value for 223,521.
  - `!euclid(4)` prints the pair in 133 ticks.
  - `euclid(4)` against `(5, _)` still stops with `K344`. The branch fails
    normalizing the prime, the first component, and main fails normalizing
    the whole value. The prime is deeper than the kernel's syntax-depth
    guard, and the note says the marks cannot change that.
- **Bare hole and eta.**
  - A bare `_` is refused with `E485: evaluate e expecting _; would compute
    nothing: write !_ to compute the value's weak head, or !!_ for its full
    normal form.`
  - The eta-reduced successor prints `succ`.
- **Contracts, Cubist tests and the baseline.**
  - The contracts and the Cubist tests keep their outcomes: the test suite
    checks them, `tests/evaluation-baseline.test.mjs` among it.
  - The baseline fixture, `tests/fixtures/evaluation-baseline.json` at
    version 6, carries 21 `-normal` twins among its 47 workloads.
- **`constructs.json`.**
  - Every construct is evaluated in `tests/evaluation-demand-marks.test.mjs`,
    one test per setup. Each is checked under `!_` against its recorded weak
    head, under `!!_` against the kernel's normal form, and printed
    unmarked.
  - The four assumption examples (B95–B98) are refused with `E324` before
    anything is computed.
  - Three constructs, A46b, B62 and B63, are left out of the `!!_` check for
    their cost: their full normal forms are the last three rows above. Each
    completes within the budget, about 71M to 73M ticks, and equals main's.
- **A lazy result is visibly distinct, and nothing expires.**
  - A suspended part is printed as a marker, `<unevaluated>`, `<fun>` and
    the like. A full normal form has none.
  - A value form is decoded and printed while its directive runs, and the
    REPL, the CLI and a checked file keep only the text. No handle outlives
    the directive, so no later session operation can force a suspended part,
    and no expiry error is needed.
  - The workbench evaluates nothing itself, and its trace already names its
    WHNF and Normalize steps.
- **Language reference.** The marks are documented as the note lists.
  - Chapter 12's `evaluate`, chapter 13's checking, chapter 17's weak head
    and chapter 18's errors.
  - The first-proof and terms transcripts, migrated to `!!`.
  - The REPL help and the quick reference.

  `tests/reference-examples.test.mjs` checks their examples.

## A regression this report found

The first branch run gave the small inverse's normal form 70,913,344 ticks
against main's 71,027,452. The digest was the same, so the normal form was
the same up to bound names.

The difference was not in evaluation. Pruning the bindings of the driver's
guide questions, added in #304 for the typed pattern's comparison, also
applied to the search's guide. The search's guide then kept more answers,
spent its fuel elsewhere and steered the search differently. Checking the
setup's imports and definitions asked the kernel 2 to 17 percent more:

| Setup step | Main | Before the fix |
| --- | ---: | ---: |
| `import fractions;` | 1,899,423 ticks | 1,944,336 ticks |
| `import binary_integers;` | 1,237,714 ticks | 1,368,846 ticks |
| `def small_inverse` | 36,144 ticks | 42,185 ticks |

A bisection of the driver found the commit. #304 now prunes only differ's
questions (`69bb116c`), and every counter above is main's again. Review round
14 of #304 confirmed that the search's memo keys, answers, fuel accounting
and kernel counters equal main's.

## Reproducing

```
node docs/roadmaps/runtime/evaluation-demand-marks/report.mjs
node docs/roadmaps/runtime/evaluation-demand-marks/report.mjs --root=MAIN_CHECKOUT
```

Each side takes about three minutes. A case's id, as `small-inverse-normal`,
runs that case alone. The script asserts a fresh build of the checkout it
measures, so MAIN_CHECKOUT needs `make wasm` first.
