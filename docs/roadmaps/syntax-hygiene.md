# Scopes and captured syntax

Expansion must preserve binding, not spelling. Moving an expression,
renaming a surrounding binder, or importing it into a different module must
not change which declarations and local variables it refers to.

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

Local binding uses capture-avoiding nominal substitution. `scopes.mjs`
describes each binder once. A telescope's group is outside its shared domain
and inside later groups and the body. A proof statement binds in subsequent
statements, outside its own initializer. Substitution renames a binder when
necessary; for pattern, statement, and parameter binders that cannot safely
be renamed before elaboration, it refuses a capture. Unknown syntax kinds fail scope traversal
rather than silently being treated as having no binders.

`scoped` is a closure: syntax paired with its original elaboration scope.
Caller substitution and relocation cannot enter its contents. `instantiated`
retains an elaborated term abstracted over parameters; explicit arguments
reconnect it to the destination's locals. Notation is retained at the
expressions that use it, so different parents can carry different selections.

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

Homomorphism generation uses separate hole maps for declaration references,
parameter types, and expressions. Holes cannot collide with source binders.
The blanket name rewrite is removed. Closed references do not require callers
to avoid their display names; E866 remains for headers still read by name.

## Deriving requests and generated artifacts

The `deriving (...)` opt-in and capability registry are specified but not
implemented in this branch. Existing generators use the boundary above.
Future deriving machinery must preserve it:

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

`tests/references.test.mjs` checks identity preservation under substitution,
alpha renaming, relocation, serialization, and elaboration lowering; opaque
closures; structural selections; telescope and statement scopes; and unregistered syntax.
`tests/theory-resolution.test.mjs` covers imports, inheritance, derived
operations, notation, initial/free models, families, homomorphisms, and
isomorphisms with colliding source and template names.

Extend these invariants for every new binder or derivation. A transformation
must state which bindings it preserves and which explicit interface it
substitutes; checking a few example names is insufficient.
