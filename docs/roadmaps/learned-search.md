# Learned search for the instruction driver

Status: a design, nothing implemented. It builds on the instruction kernel
([kernel-instructions.md](kernel-instructions.md)), whose driver searches for
conversion steps in JavaScript, and it reuses the ideas of the original THTH
(2023–2025: a Rust opcode driver and PyTorch models over its ASTs). The
second half of this note says which of THTH's architectures carry over.

## Why this search suits learning

The instruction kernel makes reinforcement learning unusually clean:

- **The kernel is the referee.** An action is legal only if the kernel
  accepts the instruction. An equality goal is closed only when its two sides
  are alpha-equal. Rollback is a checkpoint. Reward hacking is impossible,
  and soundness is untouched: the network is as untrusted as the driver.
- **The environment is fast.** The whole archive derives in 14 s, so a laptop
  runs millions of kernel-checked steps an hour.
- **The graphs are the tensors.** The syntax hash graph is the network's
  input, and the judgement hash graph is its output: THTH's two graphs again.

## What to optimize

Coverage is the wrong target: of the 138 archive definitions that do not
derive, 134 wait on kernel rules (pushouts, overlapping faces, W types, Glue,
`HComp`) and 4 on search. Two objectives are real:

1. **Cheaper derivations.** Highlighted steps instead of normalizing whole
   types (decision 4 of the instruction kernel). The heuristic driver never
   optimizes derivation cost.
2. **Independence from the oracle.** The driver's congruence choice consults
   `cc_kernel_convertible`, the term checker's conversion, as a search aid. A
   learned value head can replace it, so the driver stops depending on the
   old reduction machinery for guidance.

**The cost must be kernel effort, not instruction count.** Priced by
instructions, a policy learns "always `Normalize`" in one step. The kernel
resets its operation counter from `operation_budget` at every instruction,
so the work of one instruction is exactly measurable; the bridge should
expose it. `Normalize` then prices itself out where a short step would do.

## The decision problem

The typing derivation stays classical: `deriveNode` has one rule per node
kind. Learning enters only where two types must agree, the driver's `agree`.

- **State.** An equality goal: the two sides, the context entries they use,
  and the entries' types.
- **Actions.** At a node on one side: `beta`, `iota`, `path`, `delta`,
  `whnf`, eta expansion, or descend (congruence at that node). At the goal:
  `symmetry` and `normalize`. Legality is syntactic (a `beta` needs an
  application of a lambda, a `delta` a definition reference), so masking
  needs no kernel call.
- **Episode.** One `agree` call. Descending makes the parts independent
  subgoals, each its own episode, as in HyperTree Proof Search; a goal
  closes when all of them do.
- **Reward.** The kernel cost of the instructions issued, negative, plus a
  bonus on closing. A failed episode pays the fuel it burned.
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

No linear position, and no symbol or definition ids.

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

1. **Subtree stage, memoized.** Two layers using only the first three heads.
   A token's output then depends only on its subterm, so it is computed once
   per interned node and cached for the life of the kernel, exactly like
   hash-consing. A branch point encodes only nodes it has never seen; the
   session amortizes the rest, and common types and lemmas are embedded once.
2. **Goal stage.** Two layers with every head. This is where "what am I being
   compared against" enters, through the cross-side and ancestor heads, and
   where near-matches that become equal after a few steps get learned.

### Output heads

- **Policy.** Per token, logits for `beta`, `iota`, `path`, `delta`,
  `whnf`, eta and descend on that token's side; on the goal token,
  `symmetry` and `normalize`. Illegal moves are masked. One softmax over all
  legal moves is the search prior, like Go's per-intersection head.
- **Value.** On the goal token, with THTH's pairing of the two sides' root
  tokens as `(a, b, a − b)`: the probability of closing within budget, and
  the log of the remaining kernel cost.

### Size and cost

| | Width 64, four layers |
| --- | --- |
| Parameters | about 120k (four layers of 25k, plus 20k of embeddings and heads) |
| Weights as float32 JSON | under 500 KB |
| A goal of 30 tokens | a few ms in plain JavaScript, under 1 ms with WASM SIMD |
| A goal of 100 tokens | about 20 ms in plain JavaScript, a few with WASM SIMD |

Attention is quadratic in tokens, which is fine at these sizes (THTH capped
expressions at 254 nodes on an H100). The net decides only at branch points
where the heuristic is unsure, as AlphaGo used its slow policy. There is
also an offline mode: search once for a cheap derivation of each definition
and keep the instruction list as a certificate, so checking never pays for
the network.

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
    pretraining and convertible pairs by construction: a term and its
    reducts are equal, terms from different walks mostly are not, and the
    oracle labels the rest.
  - Split by module, held out, or the numbers mean nothing.
- **Objectives.**
  - Imitation: cross-entropy on the expert's choice.
  - Value: closes-within-budget, and the log of the remaining cost.
  - Auxiliary labels the kernel gives for free, which teach the subtree
    stage semantics rather than syntax: whether two subterms are convertible
    (contrastive, labeled by the budgeted oracle), the head kind after
    `whnf` (one instruction), and whether one term is a witness of another
    (THTH's judgement recognition, read off the judgement graph).
- **Expert iteration.** Search with the policy as prior and the value in
  place of the oracle; keep every derivation cheaper than the heuristic's;
  retrain on those; repeat. This is AlphaZero's loop, and HyperTree Proof
  Search's on and-or goals.
- **Tooling.** PyTorch for training with dense masks and
  `scaled_dot_product_attention`; no graph library and no custom kernel at
  this scale. Weights export to JSON. Inference is a few hundred lines of
  `Float32Array` code in the driver, and WASM SIMD only if it matters.

## Phases

1. **Options.** Refactor `agree` so each branch point is an explicit list of
   options with a pluggable chooser. Useful regardless: the workbench can
   show the options, and the policy plugs in later.
2. **Logging and cost.** The bridge exposes the kernel cost of each
   instruction; the coverage tool logs trajectories and reports total cost
   per definition. This is the baseline.
3. **Imitation and ablations.** Train the network on the logs; measure
   agreement with the heuristic on the held-out modules. Run the ablation
   table below at this phase, where a run is minutes, and fix the
   architecture before expert iteration.
4. **Expert iteration** on derivation cost, measured on the held-out modules
   against the heuristic, with the oracle switched off.
5. **Deployment.** The chooser in the driver, the options in the workbench,
   and the offline certificate mode.

Phases 1 and 2 are a day or two and stand on their own. The experiment is a
week, and it may not beat the heuristic on the current corpus, which is why
cost, not coverage, is the objective. The search space grows a lot with
pushouts, Glue and `HComp` (stage 3 of the instruction kernel), and that is
when hand heuristics stop scaling; the experiment pays off most after stage
3 lands.

## What THTH's architectures offer

The original THTH trained an AST transformer on an H100 (six layers, width
1024, sixteen heads, a 2048-dimensional latent, 100 million random-walk
steps). Its pieces, and whether they carry over. "Adopted" means adopted
into the starting hypothesis; many of these may be ablated away, and the
[Ablations](#ablations) section says how each is tested.

**Adopted.**

- **Topological attention**, one boolean mask per head and sample, built from
  ancestor, descendant, parent, child and binder relations, with a custom
  CUDA kernel for it. This is the core of the design above. It beats plain
  message passing here: the ancestor and descendant heads reach a whole spine
  in one layer, where a graph network needs one layer per hop, and a cross
  side head is just one more mask. The masks are THTH's
  `transformer_heads_config.py` with the output and mixed variants dropped,
  since nothing is decoded.
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
  targets for `Replace`. Both are stage 4 of the instruction kernel, when
  tactics issue instructions directly.
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

- the heuristic driver as it stands, with and without the oracle;
- a uniform random policy under the same search, to measure how much the
  search alone does;
- a linear policy over the syntactic features with no attention, the
  cheapest learned baseline.

**Metrics**, on the held-out modules: derivation cost against the heuristic,
coverage (must not drop), agreement with the expert at branch points, and
time per branch point.

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

The oracle switch is the main experiment rather than an ablation: the value
head replaces `cc_kernel_convertible` only if held-out cost and coverage
hold with it off.
