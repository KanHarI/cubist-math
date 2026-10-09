# FG5 public interfaces and source provenance

G5 and G9 are active regressions; no gap fixture remains an expected failure.
Source aliases carry a resolution `key`, a public `name` and the written
binder's range separately. Registration, environment filtering and use-site
recording compare the key and term identity. Formatting uses the public
name; navigation uses the binder origin, while each link retains its own
occurrence range. Match rebinding preserves the complete alias record.
Derived parameter tokens now retain their public label as well as the
declaration's parameter metadata.

The linter recognizes operation/law type telescopes as public interfaces.
It suppresses W705/W706 arrow advice on those binders because removing them
can disable Hom/Iso and initial/free generation. It continues traversing
their domains and other expressions, and ordinary safe advice remains.
Tests check named Hom constructors, identity/Iso, initial/free folds,
computations, artifact sets and absence of assumptions before and after
the remaining safe suggestion.

## Fixture correction

FG0's G5 fixture added `S.op(x := a, y := a)` to the inventory source, but
named model-member arguments are not supported by the language. That client
already failed E378 before a lint rewrite and therefore masked the actual
defect. FG5 replaces it with the existing supported named `T.Hom.make`
interface. The corrected original checks on FG4 before this lint fix;
the proposed arrow rewrite still loses Hom and initial capability. A
separate regression checks this distinction explicitly. This phase does
not add named model-member or inductive-constructor calls.

## Producer and consumer audit

| Boundary | Evidence |
| --- | --- |
| Capture/freshening and generated parameters | Existing alpha-renaming labels survive; complete derived parameter tokens now expose their label to source binding registration. Semantic reference identities remain independent. |
| Alias registration and filtering | Internal keys identify environment entries; a public spelling never substitutes for a key in an equality test. Term identity disambiguates shadowing. |
| Use-site records and navigation | Every G9 binder/use keeps `c`, its own range and the original binder target. Imported source aliases navigate to their source module. |
| Inspection | Hover expression/context labels and CLI signatures contain no private `c1` or capture keys. Native term/context keys remain private implementation data. |
| Synthetic provenance | Existing synthetic-link suppression is retained; generated signatures remain inspectable without claiming written tokens. Existing multiplicity/import tests remain active. |
| Refusal diagnostics | G10 retains the actual conflict token and nonempty range; G12 distinguishes checked earlier value calls from real type-unfolding refusal. CLI verifies the focused E871 category and public field name. |
| Lint | Only public operation/law telescopes suppress arrow advice. A remaining safe ordinary rewrite preserves checked clients and generated artifacts. |

`frontend-provenance.test.mjs` adds direct/imported law and derived-parameter
link/hover checks, checked lint clients and CLI observations. The inspector
browser test puts G9's binder and uses on different lines, checks all four
labels and expressions, and navigates each use to the written binder line.
