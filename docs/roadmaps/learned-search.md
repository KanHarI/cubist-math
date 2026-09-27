# Learned search for the instruction driver

Status: optional research design, reviewed on 2026-09-27. Phases 1 and 2
are delivered (2026-09-27): the driver's branch points list their moves for
a pluggable chooser, and the kernel counts its work; see
[Phases](#phases) for the baseline they measured. The learning phases 3–5
are unimplemented. It builds on the instruction kernel
([kernel-instructions.md](kernel-instructions.md)), whose driver searches for
conversion steps in JavaScript, and it reuses the ideas of the original THTH
(2023–2025: a Rust opcode driver and PyTorch models over its ASTs). The
second half of this note says which of THTH's architectures carry over.
No language release or kernel feature depends on this experiment.

## Why this search suits learning

The instruction kernel makes reinforcement learning unusually clean:

- **The kernel is the referee.** An action is legal only if the kernel
  accepts the instruction. An equality goal is closed only when its two sides
  are alpha-equal. Rollback is a checkpoint. Kernel acceptance preserves
  soundness; rewards and resource accounting still need checks against
  misleading optimization. The network is as untrusted as the driver.
- **There is a working baseline.** The K1.4 measurement before L1.1 checked
  the archive with the driver's own guide in 37 s, against 34.9 s with the
  old conversion oracle. The 2026-09-27 review at `fabb174` recorded zero
  gaps, a 30.7 s archive check and all 3,916 stored definitions re-derived
  in 10.7 s with the default guide. These are single-run observations,
  not training-throughput measurements; rerun them for each comparison.
- **The graphs are the tensors.** The syntax hash graph is the network's
  input, and the judgement hash graph is its output: THTH's two graphs again.

## What to optimize

The driver already derives the archive, including pushouts, W types, Glue
and `HComp`. Its own guide is the default; K1.4 delivered independence from
the old conversion oracle. Coverage must remain unchanged. The experiment
has two objectives:

1. **Cheaper derivations.** Highlighted steps instead of normalizing whole
   types (decision 4 of the instruction kernel), where measurements show a
   lower total cost than the current heuristic.
2. **Cheaper guidance.** Compare a learned chooser with the driver's own
   guide, including the cost of inference. The optional
   `cc_kernel_convertible` guide remains a historical comparison while it is
   available; replacing it is no longer an outstanding prerequisite.

**The cost must be kernel effort, not instruction count.** Priced by
instructions, a policy can prefer `Normalize` solely because it takes one
instruction. The kernel resets its remaining budget from `operation_budget`
at instruction entry. That reset alone does not define a complete cost:
specify which work consumes the budget, whether nested operations reset it,
and how failures, retries and queries are charged before exposing telemetry.
Use cumulative counters whose deltas survive errors and rollback, and test
their accounting against direct instruction calls. Include failed search,
guide queries, inference time and cache/session state in the comparison;
measure end-to-end checking time as well as kernel effort. Share this work
with L1.3's deterministic-fuel accounting.

## The decision problem

The typing derivation stays classical: `deriveNode` has one rule per node
kind. Learning enters only where two types must agree, the driver's `agree`.

- **State.** An equality goal: the two sides, the context entries they use,
  and the entries' types.
- **Actions.** At a node on one side: `beta`, `iota`, `path`, `delta`,
  `whnf`, eta expansion, or descend (congruence at that node). At the goal:
  `symmetry` and `normalize`. Syntactic masks remove obvious mismatches
  (a `beta` needs an application of a lambda, a `delta` a definition
  reference); the kernel checks the remaining side conditions.
- **Episode.** One `agree` call. Descending creates subgoals with the
  appropriate binder and face contexts; a goal closes when all its parts
  do. Define shared budgets, rollback and reconstruction before treating
  subgoals as separate training episodes.
- **Reward.** The kernel cost of the instructions issued, negative, plus a
  bonus on closing. A failed episode pays the fuel it burned; splitting a
  goal cannot multiply the closing bonus.
- **Terminal test.** Alpha equality, from the kernel.

## The network

A small transformer over the kernel's own graph, in THTH's topological form:
plain multi-head attention where each head has its own boolean mask, built
from a structural relation between tokens.

This is the starting hypothesis, not a settled choice. THTH's pieces were
designed for a much larger model on random-walk data, and none has been
tested on this task at this scale. Each one is listed under
[Ablations](#ablations) with the experiment that keeps or removes it, and
the first draft of this design, a message-passing network, stays as the
control.

### Tokens

- **Syntax nodes** of both sides, one token per interned node and side. A
  subterm on both sides is one node with two tokens that share the first
  stage's embedding, so exact matches are visible for free.
- **Context entries** as binder tokens, THTH's artificial binder nodes. In
  the instruction kernel a bound variable *is* a context entry, so the
  entry's id is the binder token, and occurrences link to it.
- **A goal token** for the whole state (THTH's control token).
- **A few register tokens**, free compute with no input (THTH's brain
  matter).

### Features

Relational, never identities, so the net transfers to modules it never saw:

- the kind, one of about 40, and the universe level;
- a variable: which entry binds it, as a distance along the path to the root,
  and whether that entry is shared by both sides;
- a definition reference: arity, body size, the head kind of its body,
  whether it recurses, and whether it is defined later than the references on
  the other side (the lazy-delta signal);
- a formula: endpoint, single dimension or compound, and whether both sides
  carry the same one;
- a numeral collapses into one token with a log-scale count, so 10! is not a
  chain of 3.6 million `Succ` nodes;
- depth, the child slot under the parent (THTH's relation to parent), and
  which side or sides reach the node.

No linear position, and no symbol or definition ids. Goal-relative features
(the opposite side, sharing between sides, root depth, binder distance and
parent position) enter only the goal stage. A shared node can have several
parents and occur at several depths; the tensorizer must represent those
relations without inventing a unique occurrence.

### Heads

Each attention head sees one relation. Per token, the mask admits:

| Head | Admits | From THTH |
| --- | --- | --- |
| descendants | every node below it | `INPUT_TOPOLOGICAL_BOTTOM_UP` |
| children | its immediate children | `INPUT_TOPOLOGICAL_CHILDREN` |
| binder to occurrences | the variables an entry binds | `INPUT_BOUND_TOPO_CHILDREN` |
| ancestors | every node above it | `INPUT_TOPOLOGICAL_TOP_DOWN` |
| parent | its parent | `INPUT_TOPOLOGICAL_PARENTS` |
| occurrence to binder | the entry that binds it | `INPUT_BOUND_TOPO_PARENTS` |
| cross side | every token of the other side | new |
| goal | the goal and register tokens, both ways | control token, brain matter |

Two additions to THTH's layer: a per-head bias by relative depth (a parent
is one step up, a great-grandchild three down; THTH encoded only absolute
depth), and `ghostmax`, THTH's softmax with a ghost zero logit, so a head
with nothing relevant attends to nothing.

### Two stages

1. **Subtree stage, memoized.** Two layers using intrinsic node features
   and relations entirely within that subtree. Outside context entries,
   root-relative positions and other-side features cannot enter this stage.
   Cache by kernel session, immutable node content and model/feature version;
   invalidate on rollback if handles can be reused, and bound cache memory.
   Compare cached and fresh embeddings across goals and binder contexts.
   Reuse is valid only after those outputs agree.
2. **Goal stage.** Two layers with every head, adding the context, occurrence
   and opposite-side features above. Binder-to-occurrence relations spanning
   the goal belong here. This stage is recomputed for each goal.

### Output heads

- **Policy.** Per token, logits for `beta`, `iota`, `path`, `delta`,
  `whnf`, eta and descend on that token's side; on the goal token,
  `symmetry` and `normalize`. Illegal moves are masked. One softmax over all
  legal moves is the search prior, like Go's per-intersection head.
- **Value.** On the goal token, with THTH's pairing of the two sides' root
  tokens as `(a, b, a − b)`: the probability of closing within budget, and
  the log of the remaining kernel cost.

### Size and cost

Width 64 and four layers are a starting configuration. Parameter count,
serialized weight size, memory use and inference latency remain unmeasured;
text JSON does not have the size of packed float32 data. Measure these on
actual goal-size distributions in the CLI and browser before deployment.

Attention is quadratic in tokens. Set token and memory limits with a
deterministic heuristic fallback. A chooser may run only at selected branch
points if that improves total checking time. An optional offline mode could
retain instruction certificates; it needs versioned serialization and
replay checks before claiming that checking avoids network inference.

### The first draft, kept as the control

The design before reviewing THTH was a message-passing network over the same
relations: a bottom-up gated encoder memoized per interned node (a node's
vector from its features and its slot-projected children), two weight-shared
goal iterations passing messages down the tree, along binder edges and from
a pooled goal vector, and one cross-attention layer between the sides, at
about 85k parameters. Masked attention replaced it because the ancestor and
descendant heads reach a whole spine in one layer, where message passing
needs a layer per hop, and because the cross-side comparison becomes one
more mask instead of a separate layer. That reasoning is plausible, not
measured, so the draft is the first ablation arm: the same features, the
same edges, and the same heads, with message passing in place of attention.

## Training

- **Data.**
  - Expert trajectories: the heuristic driver's `agree` calls over the
    archive, logged with each branch point's options, the choice, and the
    kernel cost of the resulting instructions.
  - Random walks: legal random instructions over `InstructionGraph`, THTH's
    random walker over its opcode driver. They give typed terms for
    pretraining and positive conversion pairs by construction: a term and
    its reducts are equal. Terms from different walks are unlabeled until
    checked; different generation histories are not negative evidence.
  - Preserve three outcomes from budgeted guidance: equal, different and
    unknown. Exhaustion, errors and syntax unsupported by the old oracle
    (including G0) remain unknown and are excluded from binary labels.
  - Split by module and audit shared imported trajectories to avoid leaking
    held-out goals. Separate training, validation and final test modules.
- **Objectives.**
  - Imitation: cross-entropy on the expert's choice.
  - Value: closes-within-budget, and the log of the remaining cost.
  - Auxiliary labels from checked results: positive conversion certificates,
    definitive negative comparisons within the guide's supported fragment,
    the head kind after a successful `whnf`, and known witness judgements
    from the graph. Charge label-generation work and preserve unknowns.
    Absence from the judgement graph does not establish a negative witness.
- **Expert iteration.** Search with the policy as prior and compare value
  guidance with the current heuristic; retain cheaper checked derivations
  from training modules, retrain and repeat. Validation chooses the model;
  final test trajectories never enter training.
- **Tooling.** PyTorch for training with dense masks and
  `scaled_dot_product_attention`; no graph library and no custom kernel at
  this scale. Prototype weight export and `Float32Array` inference in the
  driver; consider WASM SIMD after measuring the prototype.

## Phases

1. **Options.** Done on 2026-09-27. Each branch point of `agree` is an
   explicit list of moves (normalize, descend, a step on either side or
   both, whnf, eta), and a chooser ranks them
   (`heuristicChooser` in `web/cubical-instruction-driver.mjs`). The
   heuristic is the driver's former order; the archive's elaboration
   fingerprint is identical under it. The workbench does not show the
   options yet.
2. **Logging and cost.** Done on 2026-09-27. The kernel counts
   instructions and queries, their steps of budget and their failures,
   cumulatively (`cc_kernel_work`, `CubicalKernel.work()`; the accounting is
   in [kernel-instructions.md](kernel-instructions.md#the-driver)). The
   coverage tool reports the work of the archive check and of each
   definition derived again, rejected instructions and guide queries
   included, and the outcome of each move; `--trajectories=FILE` writes
   every branch point of every derivation, with the kernel steps spent
   choosing and moving (`tools/search-telemetry.mjs`). The report pins the
   revision, machine, budgets and session mode. The baseline below was one
   run on an Apple M3 Pro shared with other jobs, at `d44239e` with these
   changes; times are observations, and the counts are deterministic.

   | Kernel work | Archive check | Derived again |
   | --- | --- | --- |
   | Time | 40.5 s | 14.4 s |
   | Instructions (rejected) | 5,329,388 (31,706) | 2,012,235 (43,704) |
   | Instruction steps | 167.5 M | 130.6 M |
   | Queries (failed) | 512,673 (1,093) | 289,326 (1,153) |
   | Query steps | 21.1 M | 16.9 M |
   | Exhausted budgets | 1,101 | 1,160 |
   | Branch points | 2,137,692 | 835,564 |

   Of the 842,375 moves made while deriving again, 84% were steps, which
   always apply; descending agreed 68,638 times and failed 50,865 times;
   whnf and eta changed nothing 8,339 times. Peak memory was 2.4 GiB.

   The trajectories show where the cost is. Seven normalize moves ran out
   of their instruction's full budget of 10M steps and failed: 70M of the
   147M steps of deriving again, 47%, in seven definitions, each of which
   then agreed by other moves. A chooser, or a smaller budget for a
   speculative normalization, that avoided them would save more than any
   ranking of the cheap moves could.
3. **Imitation and ablations.** Train the network on the logs; measure
   agreement with the heuristic on validation modules. Run the ablation
   table below and choose the architecture before final test evaluation.
4. **Expert iteration** on derivation cost, measured on the held-out modules
   against the heuristic, with the oracle switched off.
5. **Deployment.** The chooser in the driver, the options in the workbench,
   and the offline certificate mode.

Phases 1 and 2 stand on their own as driver inspection and measurement work;
the [work plan](work-plan.md#stage-1-goals-diagnostics-and-inference)
schedules them with L1.3, whose deterministic fuel is the same cost
accounting. Phases 3–5 wait for evidence that search choices account for enough cost to
justify learning. Instruction-kernel stage 3, including pushouts, Glue and
`HComp`, has already landed; it supplies existing benchmark cases. Future
declared inductive types may supply more cases, but their delivery does not
wait for learned search. No schedule or speedup is established yet.

## What THTH's architectures offer

The original THTH trained an AST transformer on an H100 (six layers, width
1024, sixteen heads, a 2048-dimensional latent, 100 million random-walk
steps). Its pieces, and whether they carry over. "Adopted" means adopted
into the starting hypothesis; many of these may be ablated away, and the
[Ablations](#ablations) section says how each is tested.

**Adopted.**

- **Topological attention**, one boolean mask per head and sample, built from
  ancestor, descendant, parent, child and binder relations, with a custom
  CUDA kernel for it. This is the core hypothesis above. The ancestor and
  descendant heads reach a whole spine in one layer, where a graph network
  needs one layer per hop, and a cross
  side head is just one more mask. The masks are THTH's
  `transformer_heads_config.py` with the output and mixed variants dropped,
  since nothing is decoded. Whether that improves cost or accuracy over
  message passing remains an ablation result to measure.
- **Artificial binder nodes** (`LAMBDA_1`, `PI_1`, `IND_NAT_1`, …), tokens
  for bound variables that occurrences attend to. Here they are the context
  entries, which the instruction kernel already has.
- **The embedder's channels**: label, numeric parameter, bound link, depth,
  and child slot. Dropped: the linear position embedding, which is noise for
  a graph (THTH randomized node order to make it so). Added: definition,
  formula and numeral features.
- **Brain matter tokens**, free registers in the padding, and the control
  token: the goal and register tokens.
- **`ghostmax`**, a softmax that can attend to nothing.
- **The pair features `(a, b, a − b)`** of the judgement-recognition head and
  of `JudgementsTransformerBlock`, for the value head. Its position-wise
  pairing of two ASTs needed aligned trees; the cross-side head does not.
- **The random-walk data generator** over the opcode driver, now over
  `InstructionGraph`.
- **Code.** The PyTorch modules (masked attention, MLP, `ghostmax`,
  `AttentionToVec`, the embedder pattern) lift almost verbatim. The
  tensorizer does not: it walks THTH's HoTT AST with de Bruijn references and
  `IndNat`/`IndEq`/`IndW` binders, and the cubical kernel has named binders,
  formulas, `Comp`, `HComp` and `Glue`.

**Not now.**

- **The AST VAE**: an encoder pooled to a 2048-dimensional latent, a KL
  cost, and three decoders (BERT-style masked nodes, top-down autoregressive
  where each node sees its ancestors, bottom-up where each sees its
  descendants), with reconstruction losses per channel. Conversion search
  generates nothing and retrieves nothing, so none of this is needed. It
  returns for two later uses: **premise selection**, where a latent space
  with THTH's judgement and context banks as retrieval memory (the
  `rag_latent_space_config`) finds relevant lemmas for tactics; and **term
  generation**, where the top-down decoder proposes motives for induction or
  targets for `Replace`. These are separate future tactic experiments;
  instruction-kernel stage 4 is already delivered and requires neither.
- **The register-machine agent** (`RegistersDriver`): judgement and
  context-fragment registers, banks, highlight switches, moves between them,
  `RunOpcode` reading operands from fixed registers, and win conditions
  (`CreateProposition`, `ProveOneOff`). It is a general prover with a small
  fixed action vocabulary, at the price of a cursor walk before every
  opcode. For conversion, per-token action heads decide in one step. The
  register design is worth revisiting for the tactic-level agent, where the
  operands really are earlier judgements.
- **The CUDA topological flash attention and LoRA attention**: training aids
  at width 1024. At width 64, dense masks in PyTorch suffice.
- **Spectral graph convolution** (Laplacian eigenvectors per head mask,
  Chebyshev filters) and the **DNA-style linear tokenizer** (many tiny tokens
  with a causal transformer): both marked "not in current use" in THTH, and
  both lose what the masks keep.

THTH never reached a policy: its last experiments trained the VAE with the
judgement-recognition loss as the foundation for an agent. The instruction
kernel supplies what that agent lacked, a cheap exact referee with a real
corpus, so the policy can start small.

## Ablations

The rule: start from the smallest network that works, add one piece at a
time, and keep a piece only when it improves the held-out numbers by more
than the run-to-run noise (three seeds each). THTH's pieces earned nothing
yet on this task; a design inherited whole would carry every one of its
accidents. Results go into the table as they arrive.

**Baselines**, without which no ablation means anything:

- the heuristic driver as it stands, with its own guide and with the
  term checker's conversion as the guide (`node tools/instruction-coverage.mjs`
  and `--oracle`; on 2026-09-27 the archive checked in 37 s and 34.9 s,
  and without any guide on 2026-09-26 in 62 s, with three declarations out
  of kernel budget);
- a uniform random policy under the same search, to measure how much the
  search alone does;
- a linear policy over the syntactic features with no attention, the
  cheapest learned baseline.

**Metrics**, on the held-out modules: derivation cost against the heuristic,
coverage (must not drop), agreement with the expert at branch points,
inference latency, total checking time and peak memory. Report unknown
labels and budget failures separately.

| Piece | Ablation | Should matter for | Result |
| --- | --- | --- | --- |
| Masked attention | message passing over the same edges (the first draft) | deep spines; otherwise the draft is cheaper | |
| One head per relation | one head with the union mask and a relation-type bias | cost per layer | |
| Ancestor and descendant heads | parent and child heads only | deep terms | |
| Binder tokens | drop them; keep the binder-distance feature | eta and replacement under binders | |
| Cross-side head | drop it; the goal token carries the other side | congruence choices | |
| Goal and register tokens | mean pooling instead of the goal token; no registers | the value head | |
| `ghostmax` | plain softmax | heads with empty masks, such as the root's ancestors | |
| Relative-depth bias | absolute depth only, as THTH | telling children from great-grandchildren | |
| Two stages with memoization | four goal-stage layers | speed only; must cost no accuracy | |
| Numeral collapse | a capped chain of `Succ` nodes | arithmetic modules | |
| Definition features | drop later-than, recursion and head features | lazy delta choices | |
| Pair features `(a, b, a − b)` | the goal token alone | value accuracy | |
| Auxiliary losses | drop each of convertibility, `whnf` head, witness | sample efficiency, held-out generalization | |
| Random-walk data | the corpus alone | pretraining the subtree stage | |
| Width and depth | 32 against 64; two layers against four | everything, at cost | |

The main deployment gate is improvement over the default heuristic with
the old oracle off: held-out coverage must hold, and measured total cost
must improve after inference and failed search are included. Otherwise keep
the heuristic; phases 1 and 2 remain useful independently.
