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

The named-rule producer remains opt-in. Lazy operands used as selection
receivers still require a source description that preserves both their term
and selection-namespace interpretations. Such rules are refused at retention
until that contract is implemented; treating an already resolved term operand
as a selector could silently choose a same-named model over a notation.

The eight authorized external CB2 rounds are exhausted. Subsequent implementation
checks are not an additional external round or evidence of a clean external
re-review.
