# Capture-binding review obligations

The CB2 reviews repeatedly exposed gaps in shared contracts. A fix is complete
only when the representation and every affected consumer preserve the missing
distinction. A passing reproduction alone does not establish that.

| Recurring root | Evidence across CB2 rounds | Contract to preserve |
| --- | --- | --- |
| Incomplete semantic data | Round 1: builtin/missing equality and omitted carrier universes/evidence. Rounds 2–4: grouped domains and anonymous term/universe positions. | The canonical representation carries every semantic position, including anonymous binders. Equality ignores display labels and source spans only where they are nonsemantic; it preserves reserved names, failures, binder correspondence and universe positions. |
| Consumers independently re-derive a source decision | Round 2: telescope/evidence order and fixed namespaces. Rounds 5–8: parent selections, operand receivers, file activations and replay disagree about the selection namespace. Round 7: notation validation and production disagree about meaningful operand views. | One source contract determines the expanded telescope, fixed references and selection classification. Consumers use its result. A receiver classified as a namespace or notation cannot later become an ordinary value through spelling lookup. Unknown inventories are not empty inventories. |
| Occurrence identity is confused with semantic identity or availability | Round 1: refused constructor identities. Round 2: parent Hom availability. Round 5: a query translator creates a different identity table. Round 6: distinct activation occurrences make equal source receivers unequal; unused namespace members affect sharing. | Identities belong to one compilation. Occurrence provenance, semantic captures and checked availability are separate. An attached notation's semantic context includes both receiver and rule-extension identity. Conditional uses carry only the alternatives they consume, and availability comes from explicit checked receipts/support plans. |
| Source ownership is lost at a phase boundary | Round 1: helper/inheritance failures lose the expansion site. Round 6: a deferred namespace failure loses its diagnostic. Round 7: source receiver offsets become client links. | Every transformation preserves source-qualified origins. A consumer reports expansion failures at the appropriate use and never interprets producer offsets as caller offsets. Source implementation references and caller operand references have separate observation ownership. |

Before applying fixes from a review:

1. Compare every finding with the previous rounds and group it by underlying
   contract. Record whether it is a recurrence, a new boundary of an existing
   root, or a new root.
2. Trace the information from source production through cloning, substitution,
   equality and dependency analysis to elaboration, publication and observation.
   Name where the distinction is lost before changing code.
3. Fix the shared representation or operation, then audit all consumers of that
   contract. Avoid a special case in the reproducer's consumer when another
   consumer can repeat the same loss.
4. Verify the intended result and a distinguishing incorrect result. Exercise
   static and deferred branches, source and destination collisions, copied or
   inherited syntax, and missing explicit receipts where applicable.
5. Lift a migration gate only when the entire newly admitted family meets its
   contract. Record remaining unsupported forms explicitly. Run the relevant
   integration and diagnostic checks before reporting completion.

For retained named rules, this means a source artifact with lazy operand
binders, explicit reader identities, operand-receiver syntax and optional model
attachment identity. Only the ephemeral elaboration receipt contains values or
environments. Invocation freshens the rule's owned bindings while each operand
keeps its caller scope. Written selection, file activation, operand recipes and
qualified operators use the same source classifier; deferred branches attach
extra rules only when that branch selects the declaring model. A standalone
notation opens no term labels. Model captures with different rule extensions
are distinct semantic notation contexts even when their receiver is the same.

The retained theory and named-rule producers are now the default. Lazy operands used as selection
receivers still require a source description that preserves both their term
and selection-namespace interpretations. Such rules are refused at retention
until that contract is implemented; treating an already resolved term operand
as a selector could silently choose a same-named model over a notation.

The eight authorized external CB2 rounds are exhausted. Subsequent implementation
checks are not an additional external round or evidence of a clean external
re-review.

Production integration exercised the same four roots again: complete request
headers distinguish the enclosing theory head from parameter-scoped arguments;
source selections retain parent notation and lazy missing receivers; subordinate
translators reuse the checker's compilation registry; and source provenance
survives member lowering, inferred-argument observations and flattened generated
telescopes. Support planning examines every captured pattern alternative without
counting an unused binder or activation token as an unknown dependency. These
changes preserve the existing positive and distinguishing negative clients,
rather than changing them to accommodate generated artifacts.

## CB0–CB2 simplification audit

The follow-up audit found another consequence of the recurring roots above:
old paths and descriptive metadata survived after their responsibilities moved
elsewhere. Remove these instead of making every later consumer support both.

- CB0's mutation runner had an audit mode and configurable expected outcomes,
  although every supported mutation must be killed by a previously passing
  semantic test. It now has one mode, with optional mutation IDs. The distinction
  between a semantic failure, a failed precondition and a broken test run stays.
- CB1's scope collector still forwarded declaration registration and exposed an
  unused adapter factory. Declaration registration now goes only through the
  translator's compilation registry. Collection reads that registry.
- CB2 retained the full source lexical context on every member, and remapped
  it during inheritance, for an obsolete notation-recipe fallback. The source
  producer already resolves each operand recipe before admitting the operation.
  Validation now requires that recipe. Members retain their resolved syntax and
  open-interface IDs, without a second source resolver or lexical snapshot.
- Inheritance used to build and discard a remapped tree just to validate an
  interface map. It now shares correspondence validation with the actual remap
  operation. Invalid IDs and attempts to capture a local still fail before
  allocating a child binding.
- Helper expansion no longer stores an unused pending summary, and generated
  fields no longer copy unused checking trees and `interface-check` markers.
  The builder uses the complete checking expression in the base declarations;
  publication checks enforce admission. Dependency analysis still reports
  unresolved decisions to support planners.

The audit keeps the bounded mutation/shrinking evidence, distinct checking and
analysis expressions, inert DAG snapshots, transactional observation frames and
full-prefix replay. Each protects a tested semantic or resource boundary;
replacing these with plain JSON copies, normalized types or live scopes would
lose a guarantee. This followup preserves the default producer boundaries
established by CB2; it does not start CB3.

For a synthetic interface with 40 members and 200 unrelated imported bindings,
serialized member data fell from 716,897 to 101,787 bytes after removing the
lexical snapshots (about 86%). This measures that representation change only,
not total compilation memory or runtime.

Original audit validation before CB2 production integration: 1,191 tests,
with 1,143 passes, 48 then-existing TODOs and no failures;
all 3,857 canonical corpus checks passed. All four CB0 mutations were killed
by their expected distinguishing tests. The inheritance controls also reject
unknown IDs and local-binder capture without allocating child identities.

Validation after applying the cleanup to completed CB2: `npm test` passed
with 1,193 tests, 1,177 passes, 16 documented later-phase TODOs and no
failures. All 3,857 canonical checks passed. The targeted cleanup suite
passed all 102 tests, and all four production mutation checks were killed.


## Expanded cleanup after production integration

The first simplification pass was too narrow: it removed metadata while leaving
whole superseded producers behind. This repeats the second review root above:
consumers can independently reconstruct a source decision. Once CB2's retained
producers became the default and their clients passed, keeping both producers
and propagating a mode switch through replay no longer protected a migration
boundary. It kept a second implementation of that boundary alive.

The expanded cleanup removes the nominal theory and initial/free generators,
nominal named-rule capture, the lexical capture service and its duplicate
private environment keys, and the separate model-operand descriptor interpreter.
Theory, initial/free and named-notation source entry now have one implementation.
Replay uses the same implementation without producer-mode switches. Hom shape
planning and proposition classification consume retained identities directly;
their nominal/retained symbol adapters disappear. Initial source retention and
checked-argument elaboration share one module instead of importing each other.
The reference transformation tests remain, and source-resolution assertions now
exercise the retained resolver. No semantic positive or negative client was
removed to make this cleanup pass.

Following removed producers to their consumers also exposed diagnostic strings
that the old producer alone kept visible to the catalogue scanner. Active
namespace and notation failures keep their codes; only the gone implementations
are retired. Missing literal/numeral readers report their source import advice,
and a refused model extension keeps its original diagnostic and publication
behavior. New controls check these user-visible boundaries.

The audit also examined CB0's witness controls, mutation/shrinking and cost
records, and CB1's observation frames, scope descriptions and replay ownership.
Those mechanisms have separate tested responsibilities: semantic client
comparisons, failure classification, deterministic work accounting, discarded
attempt isolation, bounded DAG serialization and full-prefix reconstruction.
The cleanup removes duplicate registration and mode propagation around them;
it does not replace those guarantees with unverified shortcuts. Historical
source rewriting remains isolated, and the Hom/Iso template adapter remains
until CB4 replaces the actual template producer. The small generated model
numeral rule remains because model numerals still consume it.

Expanded validation on frozen source: `npm test` passed 1,178 of 1,194 tests,
with the same 16 later-phase TODOs and zero failures. All 3,857 canonical checks
passed. All four production mutations were killed. The targeted retirement and
recipe suites passed 83/83 and 55/55 tests, respectively; both explicit notation
diagnostic controls passed. External Claude review has not yet run.
