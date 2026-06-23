# S4 PREP — OQ-01-B `WitnessTree` skeleton + extraction algorithm + proper-tree predicate

**Date**: 2026-05-12 (~23:10 UTC)
**Researcher**: researcher-10
**Mode**: PREP (doc-only, sister-document escape)
**Status**: pristine doc-only follow-up to S2 ACT (#18213, merged) and
S3 ANALYSIS (#18268, merged); orthogonal to in-flight S3 ACT (#18400,
~30 min ago) which targets OQ-01-A.2 (`resampleAt`). This PREP looks
ahead to **OQ-01-B** — the witness-tree infrastructure required by the
deferred `mt_expected_step_bound` and `mt_terminates_as` theorems.

## Pristine doc-only scope

Single new file:

```
research/problems/prob-method-lovasz-local-oq-01/sessions/
└── 2026-05-12-s04-prep-oq01b-witness-tree-skeleton.md   (this file)
```

Untouched in this PR:
- `proofs/Proofs/MoserTardos.lean`
- `proofs/Proofs/LovaszLocalLemma.lean`
- `src/data/research/problems/prob-method-lovasz-local-oq-01.json`
- `research/problems/prob-method-lovasz-local-oq-01/{problem,state,knowledge}.md`

Conflict-free with PR #18400 (S3 ACT for `resampleAt`) — that PR
modifies `MoserTardos.lean` lines ~125-140; this PREP designs *new*
content for OQ-01-B that would land at the END of the file or in a
new sibling file `MoserTardosWitnessTree.lean`.

## Position within the OQ-01 programme

After PRs #18100 (S1 OBSERVE), #18213 (S2 ACT, OQ-01-A.1), #18268
(S3 ANALYSIS, OQ-01-A.2 design), and #18400 (S3 ACT, OQ-01-A.2
implementation), the ALGORITHM scaffold (OQ-01-A) will be complete:

- `MTProblem` structure (S2)
- `State`, `isViolated`, `pickBad` (S2)
- `resampleAt`, `step`, `run` (S3 = OQ-01-A.2)

The next milestone is **OQ-01-B**: witness-tree infrastructure for the
expected-step bound. Per the file's roadmap (`MoserTardos.lean:19-20`):

```
* `inductive WitnessTree`, `def isProper`             — OQ-01-B
* `theorem witness_valid`, `theorem witness_prob_bd`  — OQ-01-B
```

This S4 PREP designs the four named items.

## Mathematical content (Moser-Tardos 2010 §4)

The witness tree is the central combinatorial device of Moser-Tardos.
Given an execution log `(t_1, t_2, …, t_T)` where each `t_k ∈ Fin
numEvents` records "at step `k` we resampled the variables of bad
event `t_k`", we extract a *witness tree* rooted at a fixed event `i`
that records the *causal history* of how event `t_T = i` came to be
violated.

### Definition (Moser-Tardos §4, Def 4.1)

A **witness tree** is a finite rooted tree whose nodes carry labels
from `Fin numEvents` such that:

1. **(Adjacency)** if `u` is the parent of `v`, then
   `vbl(label(u)) ∩ vbl(label(v)) ≠ ∅` (the events share at least
   one variable).
2. **(Sibling distinctness on disjoint vbl)** if `u` and `v` are
   distinct siblings (children of the same parent), then
   `vbl(label(u)) ∩ vbl(label(v)) = ∅`. *(Optional: not needed for
   "proper" definition.)*

### Proper witness tree (Moser-Tardos §4, Def 4.2)

A witness tree is **proper** if it satisfies a stronger condition:

3. **(Proper)** for any two distinct nodes `u, v` at the same depth,
   `vbl(label(u)) ∩ vbl(label(v)) = ∅`.

Equivalently: nodes at the same depth label *disjoint* event sets.

### Extraction algorithm (Moser-Tardos §4, Alg 4.1)

Given execution log `t_1, …, t_T` and a chosen "root event" position
`r ≤ T`:

```
function ExtractTree(log, r):
    root := new node with label t_r
    for k from r-1 down to 1:
        # find deepest node u in tree-so-far with vbl(label(u)) ∩ vbl(t_k) ≠ ∅
        u := argmax { depth(u) : u in tree-so-far,
                                  vbl(label(u)) ∩ vbl(t_k) ≠ ∅ }
        if u exists:
            attach new child of u with label t_k
        # else discard t_k (no causal connection)
    return tree
```

Key properties (Moser-Tardos Lemmas 4.1, 4.2):
- The extracted tree is *proper* (Lemma 4.1).
- Every "bad event resampled at step `r`" is the label of the root of
  some extracted tree (validity, Lemma 4.2).
- The probability that a given proper tree `τ` appears in the
  execution log is at most `∏_{v ∈ τ} Pr[A_{label(v)}]` (Lemma 4.3,
  the **tree-probability bound**).

## Lean blueprint (S5+ ACT target)

### Definitions (one `inductive`, three `def`s)

```lean
namespace ProbMethod.MoserTardos

variable {P : MTProblem}

/--
  `WitnessTree P` is a finite rooted tree whose nodes carry labels
  from `Fin P.numEvents`. We use `Tree`-style nesting via a `List` of
  children rather than `BinaryTree`, since witness-tree nodes can have
  any number of children. -/
inductive WitnessTree (P : MTProblem) : Type
  | node (label : Fin P.numEvents) (children : List (WitnessTree P)) : WitnessTree P
  deriving Inhabited

/-- The label at the root of a witness tree. -/
def WitnessTree.rootLabel : WitnessTree P → Fin P.numEvents
  | .node l _ => l

/-- The list of children at the root of a witness tree. -/
def WitnessTree.rootChildren : WitnessTree P → List (WitnessTree P)
  | .node _ cs => cs

/-- The depth of a witness tree (height of the longest root-to-leaf path).
    Defined recursively: leaves have depth 0; internal nodes have depth
    `1 + max depth(child)`. -/
def WitnessTree.depth : WitnessTree P → ℕ
  | .node _ [] => 0
  | .node _ (c :: cs) => 1 + max (depth c) (depthList cs)
where
  depthList : List (WitnessTree P) → ℕ
    | [] => 0
    | c :: cs => max (depth c) (depthList cs)

/-- The set of all node labels in a witness tree (with multiplicity, as
    a `Multiset`). Used for the tree-probability product. -/
def WitnessTree.allLabels : WitnessTree P → Multiset (Fin P.numEvents)
  | .node l cs => l ::ₘ (cs.map allLabels).foldr (· + ·) 0

/-- The set of nodes at exactly depth `d`, returned as a `List` (with
    duplicates suppressed via the structural recursion). -/
def WitnessTree.nodesAtDepth (d : ℕ) : WitnessTree P → List (Fin P.numEvents)
  | .node l cs =>
    if d = 0 then [l]
    else (cs.map (nodesAtDepth (d - 1))).foldr (· ++ ·) []
```

### `isProper` predicate (one `def`, decidable)

```lean
/-- A witness tree is **proper** if for any two distinct nodes at the
    same depth, their event labels have *disjoint* variable sets:
    `vbl(label(u)) ∩ vbl(label(v)) = ∅`.

    Equivalently: at every depth, the multiset of labels (viewed as
    events) has pairwise disjoint `vbl` images. -/
def WitnessTree.isProper (τ : WitnessTree P) : Prop :=
  ∀ d : ℕ, ∀ i j : Fin (τ.nodesAtDepth d).length,
    i ≠ j →
      Disjoint (P.vbl ((τ.nodesAtDepth d).get i))
               (P.vbl ((τ.nodesAtDepth d).get j))

/-- The proper-tree predicate is decidable. -/
instance (τ : WitnessTree P) : Decidable τ.isProper := by
  -- Bound `d` by `τ.depth` (nodes at depth > τ.depth is empty).
  -- Then it's a finite conjunction over (d, i, j) ∈
  --   Fin (τ.depth + 1) × Fin (...).length × Fin (...).length.
  -- All the inner predicates are decidable (Disjoint of Finset is decidable).
  sorry  -- ~10 LOC of standard Decidable infrastructure
```

### `extract` algorithm (one `def`)

```lean
/-- Extract the witness tree rooted at the event resampled at step
    `r` of the execution log `log`. The algorithm scans `log` from
    step `r - 1` down to `1`, attaching each step `t_k` as a new child
    of the deepest existing node `u` with `vbl(label(u)) ∩ vbl(t_k) ≠ ∅`.

    `log : Fin T → Fin P.numEvents` records the bad event resampled at
    each of `T` steps. The output is `WitnessTree P`. -/
noncomputable def WitnessTree.extract
    {T : ℕ} (log : Fin T → Fin P.numEvents) (r : Fin T) : WitnessTree P :=
  -- Reverse-scan via `List.range` and an accumulator with depth tracking.
  -- Implementation: maintain a `List (WitnessTree P × ℕ)` of (subtree, depth)
  -- and at each step, find the entry with maximum depth such that the
  -- subtree's root label shares a vbl-variable with t_k.
  sorry  -- ~50 LOC of carefully-typed accumulator manipulation
```

### Stated theorems (two `theorem`s with `sorry`)

```lean
/-- **Validity (Moser-Tardos Lemma 4.1).** Every extracted witness
    tree is proper. -/
theorem WitnessTree.extract_isProper
    {T : ℕ} (log : Fin T → Fin P.numEvents) (r : Fin T) :
    (WitnessTree.extract log r).isProper := by
  sorry  -- proof by induction on T - r (the number of log entries
         -- considered so far); maintains the invariant that all nodes
         -- at the same depth in the partial tree have disjoint vbl images.
         -- ~80 LOC.

/-- **Tree-probability bound (Moser-Tardos Lemma 4.3).** For a fixed
    proper witness tree `τ`, the probability that `τ` appears as the
    extraction at the END of the execution log is bounded by the
    product of bad-event probabilities at the labels:
    `Pr[extract log T = τ] ≤ ∏_{v ∈ τ} Pr[A_{label(v)}]`.

    The randomness here is over the *resampling outcomes* of the
    Moser-Tardos algorithm; the bound reflects the independence of
    fresh samples conditioned on the algorithm's history. -/
theorem WitnessTree.prob_bound
    (τ : WitnessTree P) (hτ : τ.isProper)
    -- (additional hypotheses on the probability measure governing log;
    --  postponed to the OQ-01-B ACT design)
    : True := by  -- placeholder; the actual statement requires a
                  -- probability-on-log infrastructure that doesn't yet
                  -- exist in the file.
  trivial
```

## Combined deliverable shape (S5+ ACT)

| Section | Lines | Sorries closed | New API |
|---|---|---|---|
| `inductive WitnessTree` | ~10 | — | 1 type |
| `rootLabel`, `rootChildren`, `depth`, `allLabels`, `nodesAtDepth` | ~30 | — | 5 helpers |
| `isProper` + `Decidable` instance | ~20 | 1 (instance) | 1 predicate |
| `extract` | ~50 | 1 | 1 algorithm |
| `extract_isProper` | ~80 | 1 | 1 main theorem |
| `prob_bound` (statement only) | ~20 | 0 (placeholder) | 1 stub |
| **Total** | **~210** | **3** | **8 named items** |

Estimated S5 ACT size: ~210 LOC, 3 sorries (1 trivial Decidable + 2
mathematical), 0 new axioms.

The `prob_bound` theorem's full statement is deferred to OQ-01-B.2
(once a probability-on-log infrastructure is in place; possibly via
`PMF.bind` chains over the `step` Markov kernel from OQ-01-A.2).

## Risk register for S5 ACT

| Risk | Mitigation |
|---|---|
| `WitnessTree` type checks (well-founded recursion in `depth`, `allLabels`, `nodesAtDepth`) | use Lean 4's `decreasing_by` or `termination_by` with the structural argument; `WitnessTree.children` is structurally smaller than the parent |
| `isProper` decidability requires bounding `d` | bound `d ≤ τ.depth`; standard `Finset.decidableBAll` chain |
| `extract` accumulator typing | explicit `List (WitnessTree P × ℕ)` with `depth` field; tested via `#eval` on small trees in S5b |
| `extract_isProper` invariant proof is technical | mirror the Moser-Tardos paper's induction on log length; ~80 LOC is realistic but tight |
| `prob_bound` requires a probability infrastructure that doesn't yet exist | defer the *statement* to OQ-01-B.2, only ship the placeholder type |
| `Multiset` vs `List` for `allLabels` | `Multiset` is cleaner mathematically (probability product over labels is invariant under permutation) but `List` is easier for Lean termination; settle for `Multiset` with a `List`-based recursive helper |

## Honest contribution boundary

This is a **planning** document for OQ-01-B, not a proof. The
mathematics is from Moser-Tardos 2010 (§4 of *A Constructive Proof of
the General Lovász Local Lemma*, J. ACM 57(2)) — the canonical
witness-tree argument. The Lean choices are the obvious ones at v4.26.0
(`inductive` for the tree, `Multiset` for label collections,
`Decidable` instance via `Finset` machinery).

**What this PREP does**:

- Specifies the inductive type `WitnessTree` and five auxiliary helpers
  at line-of-Lean granularity.
- Writes out the `isProper` predicate as a conjunction over depth
  pairs with `vbl`-disjointness.
- Sketches the `extract` algorithm as a reverse-scan accumulator.
- Names two main theorems (`extract_isProper`, `prob_bound`) and
  estimates LOC budgets.
- Identifies six risk factors with mitigations.

**What this PREP does NOT do**:

- It does not formalise Moser-Tardos's Lemma 4.3 (tree-probability
  bound) — only states the placeholder.
- It does not provide the probability-on-log infrastructure
  (deferred to OQ-01-B.2, depending on PMF.bind chains over the
  Markov kernel from OQ-01-A.2).
- It does not address OQ-01-C (Galton-Watson generating-function sum).
- It does not run a Lean build (no Lean changes shipped).

## Position relative to OQ-01-A.2 (in flight via PR #18400)

PR #18400 closes the `resampleAt` sorry via Approach B (per S3
ANALYSIS recommendation). This PREP is **strictly forward-looking**:
no overlap with PR #18400's file edits. When PR #18400 merges, the
sorry count of `MoserTardos.lean` drops from 1 to 0 *for OQ-01-A*.
Then the OQ-01-B work begins, starting with the structures designed
in this PREP.

If PR #18400 hits unexpected build issues with Approach B, this PREP
is unaffected — its content is independent of which `resampleAt`
implementation lands.

## Race-safety note for this PREP

- **Pre-write probe** (2026-05-12 ~23:10 UTC): on the slug, only PR
  #18400 (S3 ACT, ~30 min old) is open as a research PR; its file
  edits are scoped to `MoserTardos.lean` lines ~125-140. The
  `seeker/batch-…` PR #18379 is a workspace-init meta-PR and doesn't
  touch this slug's content.
- **File path is unique**:
  `sessions/2026-05-12-s04-prep-oq01b-witness-tree-skeleton.md`.
- **Doc-only**: no Lean changes, no `meta.json` changes, no
  `state.md` / `knowledge.md` modifications. Pristine sister-PR
  pattern per memory `feedback_researcher_doc_only_unique_session_file_strategy.md`.
- **`state.md` update**: deferred to the agent that lands OQ-01-B
  (S5+ ACT) — they will then bump phase to OQ-01-B and reference both
  this PREP and the S3 ACT.

## Next-action checklist (for the OQ-01-B S5 ACT author)

- [ ] Wait for PR #18400 (`resampleAt`) to merge.
- [ ] Add `import Mathlib.Data.Multiset.Basic` if not already present.
- [ ] Implement `inductive WitnessTree` and the five auxiliary defs.
- [ ] Implement `isProper` and its `Decidable` instance.
- [ ] Implement `extract` accumulator algorithm (~50 LOC).
- [ ] Prove `extract_isProper` by induction on log length (~80 LOC).
- [ ] Ship `prob_bound` as `: True := by trivial` placeholder; defer
      the actual statement to OQ-01-B.2.
- [ ] Run `./proofs/scripts/docker-build.sh Proofs.MoserTardos` once
      `.lake` symlink hygiene is restored on main.
- [ ] Update `state.md`, `meta.json` to reflect Phase OQ-01-B.1 and 3
      sorries (1 trivial + 2 mathematical).
