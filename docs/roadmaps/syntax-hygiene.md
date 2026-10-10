# Scopes and captured syntax

Expansion must preserve binding, not spelling. Moving an expression,
renaming a surrounding binder, or importing it into a different module must
not change which declarations and local variables it refers to.

The [frontend contracts](frontend-generation.md#shared-contracts) cover
declaration ownership, dependencies, universes, evidence and publication.
The [gap inventory](../reports/frontend-generation-gaps.md#current-status-and-fixing-evidence)
owns implementation status and regression evidence.

The frontend uses nominal syntax. The JavaScript core has named `Var`, `Pi`,
and `Lam` nodes; the C kernel uses symbols, capture-avoiding substitution,
and alpha comparison. It does not use de Bruijn indices for all bindings.
Either representation can be correct. Changing kernel binders would not
repair a capture that already occurred during source expansion.

## Resolved syntax and closures

`web/cubist/references.mjs` separates three cases:

- `name` gets its meaning from lexical scope: local binders, theory
  parameters, and abstract theory fields.
- `reference` carries a declaration identity and separate display spelling.
  Its identity is an environment key no source binder can spell. Syntax
  renaming and substitution do not visit it as a name. Display spelling
  never participates in resolution or identity comparison.
- `member` contains a receiver expression and a field label. A local model's
  `T.M` selects from that value; it is not the declaration named `T.M`.
  The selected projection comes from the receiver's checked theory.

A retained expression can be open over an explicit interface: a theory's
universes, term parameters, and earlier fields. Instantiation substitutes
these. Other globals are resolved before inheritance, inlining, or generation.
Resolution uses the complete lexical scope, including fields opened by
file-level `use` declarations. Captured entries are retained in the module's
environment for later elaboration; that storage environment must not be
mistaken for the scope where source names were written. Reconstructed
projections of the same selected model retain the same identity.

Local binding uses capture-avoiding nominal substitution. `scopes.mjs`
describes each binder once. A telescope's group is outside its shared domain
and inside later groups and the body. A proof statement binds in subsequent
statements, outside its own initializer. Substitution renames a binder when
necessary; for pattern, statement, and declaration parameter binders that cannot safely
be renamed before elaboration, it refuses a capture. Unknown syntax kinds fail scope traversal
rather than silently being treated as having no binders.
Inlining substitutes a helper through the complete declaration telescope,
result type and body before reducing its application. Derived parameters
can be freshened with their later domains, result and value while retaining
public argument labels. This protects free fields under both law binders
and derived parameters, including inherited and renamed helpers. A fixed
enclosing pattern or statement binding that would capture a field is
refused with E871 at the conflicting source token.

`scoped` is a closure: syntax paired with its original elaboration scope.
Caller substitution and relocation cannot enter its contents. `instantiated`
retains an elaborated term abstracted over parameters; explicit arguments
reconnect it to the destination's locals. Notation is retained at the
expressions that use it, so different parents can carry different selections.
A captured operator retains its whole operand tree: a later capture must
not walk into it and attach the child's notation to its numerals. A resolved
proposition used by an inlined helper is classified by declaration identity,
even when its display spelling is now bound to a different declaration.
Both directions of comparisons (`<`, `<=`, `>`, `>=`) retain that context.

Initial/free generation reads these same lexical captures. It installs no
second notation alias scope. Synthetic evaluation suppresses links through
its whole expansion, including copied rules whose offsets belong to another
module. File-level `use` takes precedence over same-spelled globals,
including later declarations, in ordinary and generated declarations alike.
Imports and changed selections must preserve the scope of retained syntax.

The retained theory also records a dependency graph over field identities,
with an explicit ordered universe/parameter interface. Edges classify
carriers, operations, laws, evidence, helpers, fixed external references
(including selected notation), builtins, holes and unresolved occurrences.
Traversal follows complete helper telescopes and values. Inheritance rebuilds
the graph through its field correspondence and preserves origin identities.
Morphism and equational generation share these facts while keeping separate
admissibility rules. Their syntax support results list mapping operations
and outstanding checking obligations; they do not infer universes or prove
preservation. Unsupported model-dependent domains are refused before Hom/Iso
emission while the base theory remains usable.

Fresh internal binder names and written labels are separate. Alpha renaming
preserves the original label through constructor lowering, diagnostics, and
inspection. Named structural selections preserve their receiver spelling
for diagnostics while resolution continues to use its identity. Synthetic
syntax, including relocated evidence and repeated header expressions, emits
no source links.

Source-alias records keep internal lookup keys, public labels and binder
origins separately. Environment filtering and use-site matching compare the
key and term identity; display reads the label, and navigation reads the
binder origin. Each occurrence keeps its written range.

## Generation boundary

The contract covers generated types, constructor domains, terms, functions,
homomorphisms, isomorphisms, and initial/free-model folds:

1. Resolve globals and distinguish local field selections before retaining
   source syntax in a record.
2. Build generated declaration references explicitly, distinguishing the
   new declarations from the enclosing scope. A child may have its parent's
   display name. Never infer this distinction from spelling or search
   arbitrary source expressions for matching names after expansion.
3. Substitute the abstract interface with scope-aware substitution. Fresh
   generated locals avoid names in every expression they surround, including
   inherited bodies and nested binders.
4. Templates put every expression and declaration reference in a fresh,
   separate hole. Parse only the template, then splice AST payloads. Even
   a one-name family index is a payload. Never serialize resolved identities
   as source text.
5. Lower references to private environment keys only at elaboration entry.
   Retained records stay resolved for subsequent derivations.
6. Check every generated declaration through ordinary elaboration and the
   kernel. Typing alone does not establish preservation of intended bindings;
   hygiene is a separate obligation.

Generated recursive calls use an explicit `recursiveCall` node. Elaboration
resolves it against the current declaration's private recursion state;
source parameters and pattern binders can hide a namespace without hiding
the recursive results. Ordinary source calls still obey lexical shadowing
and the same structural recursion checks.

Calls to an earlier recursive derived operation are a separate case. They
are retained as checked projection calls in a later derived value, distinct
from structural self-calls and unsupported type unfolding.

Checked model evidence belongs to the elaboration context. Binding/opening
a model acquires checked projections; match refinement and dimension
restriction transform the proof, its type and contributing model together.
Search can consume those terms but never treats an index hit as a proof.
Optional wildcard coherence is restricted to recursive positions, preserves
the primary located mismatch on failure and charges all attempted work.

Homomorphism generation uses separate hole maps for declaration references,
parameter types, and expressions. Holes cannot collide with source binders.
Closed references do not require callers to avoid their display names;
E866 applies to headers still read by name.

## Deriving requests and generated artifacts

The [L2.6 capability contract](core-theories.md#initial-and-free-models-l26)
owns deriving syntax, support and implementation scope. Any deriving
machinery must preserve these invariants:

- A request retains the resolved theory record, lexical context, and explicit
  parameter interface, rather than a name to look up later.
- Request arguments keep the caller's scope; stored theory expressions keep
  the theory's scope. Combining them requires explicit instantiation.
- Generated types and functions retain their inputs' references and notation.
  References among artifacts use declaration identities, including artifacts
  produced by an earlier derivation.
- Capabilities retain checked artifacts and identities. Imports, inheritance,
  and later derivations cannot re-resolve their display names. Registration
  still requires the checks and universal proofs in
  [L2.6](core-theories.md#initial-and-free-models-l26).
- Generator assignments for several carriers form a scoped telescope.
  Dependent generator families refer to earlier generator bindings through
  that interface; generated carriers and functions cannot capture them.

## Enforcement

A transformation must state which bindings it preserves and which explicit
interface it substitutes. Extend these invariants for every new binder or
derivation; checking a few example names is insufficient.

Semantic checks must distinguish intended from captured equations, verify
source labels and navigation, and inspect refusal codes and nonempty ranges.
Wildcard coherence must fit the recursive boundaries or come from checked
h-level evidence. Incompatible endpoints remain refused; explicit path
clauses keep their written bodies. Failed optional coherence preserves the
original mismatch, and nonrecursive clauses do not enter that fallback.

The [inventory](../reports/frontend-generation-gaps.md#current-status-and-fixing-evidence)
maps these obligations to distinguishing tests and fixing evidence; the
[FG6 contract](frontend-generation.md#fg6-make-preservation-tests-and-measurements-a-release-gate)
specifies the cross-transformation gate.
