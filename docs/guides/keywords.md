# Reserved names

Language keywords, built-in forms and fixed generated interface names cannot
be used for user declarations, parameters, binders, constructors, fields,
pattern variables, labels or modules. This also applies to words whose
grammar role is confined to one construct, including `def`, `law`, `set`,
`prop`, `compose`, `print`, `witness`, `nonempty` and `empty`.

The parser and source reader share the registry in
[`web/cubist/parser.mjs`](../../web/cubist/parser.mjs). The
[language reference](../../web/reference/terms.html#unit-and-void) lists every
reserved name. Universe constants such as `U0` are also unavailable as names.

`along` is an ordinary name. It acts as a separator only in
`transport value along path in family` and `lift equality along path in family`.
Both forms take expressions, with no proof-block operands. `lift` is reserved;
existing bindings of that name were renamed to `lift_`. The retired `over`
statement and standalone transport prefix are not part of the current language;
`over` is now an ordinary name.

`axiom` is reserved since K2.5 step 1 (2026-10-26): it starts an axiom
expression, the whole value of `def Name := axiom F;`
([axioms](../../web/reference/first-proof.html#axiom-definitions)). `LEM` and
`Choice` became ordinary names then: the library's `classical_axioms` declares
them, and only where nothing binds them do they fall back to the archive's
builtins over `Truncate`, and since step 4 (2026-10-28) only in an archive
module; anywhere else, such a use is refused (E491). Since step 5's
in-place migration (2026-10-29) no archive module uses them. `Truncate`,
`TruncateIntro`, `TruncateProp` and `TruncateElim` stay reserved until the
builtins are removed, so that a source using them meets that refusal rather
than an unknown name. No revision before gave `axiom` a meaning, so the
historical source reader reads a source of that time with every `axiom` as
the name it was, renamed with its declaration wherever its binding came
from, and a later source with the form (`historicalKeywords` in
`web/cubist/legacy-syntax.mjs`).

The deriving vocabulary from #187 and #198 is reserved now: `deriving`,
`isomorphisms`, `morphisms`, `free`, `initial`, `limits`, `preadditive`,
`additive`, `preabelian` and `abelian`, together with the inductive
derivations `paths`, `decidable_equality`, `universal`, `irrelevance`,
`ind_prop` and `rec`. Reserving a name does not implement its derivation.

Fixed generated names are reserved too: `Hom`, `Iso`, `cat`, `equality`,
`make`, `map`, `id`, `inverse`, `compose`, `to`, `from`, `from_to`,
`to_from`, `model`, `fold`, `fold_map`, `fold_unique`, `universal`, `gen`,
`squash`, `IsInitial`, `IsTerminal`, `IsLimit` and `IsColimit`. The compiler
and categorical foundation supply these interfaces through ordinary checked
terms; reserving their names adds no trusted proof principle.

Generated members remain usable. `T.Hom.compose(g, f)` calls the generated
composition, `T.Hom.make(map := f, ...)` names an existing generated field,
and `T.squash(...) @ i` refers to a generated constructor. These are references
to the supplied interface and introduce no user binding. Use distinct names
for your own declarations, such as `inverse_` or `model_`.

Names formed from user fields, such as `map_mul`, still need collision
checks before any generated declarations are published. Every new fixed
interface name must enter the shared registry and have conflicting user
bindings migrated before its interface is released.

The migration renames declarations and references together. In particular,
the archive module `paths` is now `paths_`, its `inverse` function is
`inverse_`, and the test module `glue` is `glue_`. The historical source
reader follows lexical scopes and known matched types when translating old
bindings, while retaining sum injections and generated constructors. A
qualified reference, `module::name`, always names a declaration, and follows
its renaming.
