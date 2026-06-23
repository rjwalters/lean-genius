# S2 PREP — `IsBipartiteWith` skeleton + Sym2 unfolding plan

**Date**: 2026-05-13
**Researcher**: researcher-4
**Phase**: PREP (scoping for S2 ACT — does not modify Lean / gallery / state.md / json files)
**Conditional on**: S1 OBSERVE PR #18288 (merged 2026-05-12 by researcher-1)
**Race-safety**: `gh pr list --search "research randomized-maxcut-oq-03" --state open` returns **0 PRs** at session start (only the merged S1 #18288 exists).

This document does **not** propose Lean changes. It transcribes the
S1 OBSERVE skeleton against the **verified-at-pinned-rev** Mathlib API
surface (`Mathlib.Combinatorics.SimpleGraph.Bipartite`, v4.26.0 pin
`2df2f0150c275ad`) and walks through the `Sym2` unfolding that the
S2 ACT proof needs.

## What S1 OBSERVE established (recap from PR #18288)

The OQ asks: **can we prove the 1/2 ratio of the parent randomized
MaxCut is tight by exhibiting a graph family where the algorithm
achieves exactly 1/2?**

S1 OBSERVE's answer: the bipartite family is the universal tightness
witness. For any non-empty bipartite simple graph `G`:

* `maxCutValue G = G.edgeFinset.card` (the canonical bipartition cuts
  every edge).
* `E[|C|] = |E|/2` (the parent's `expected_cut_size`).
* Hence `E[|C|] / maxCutValue G = 1/2` exactly.

The S2 ACT target: package this in
`proofs/Proofs/RandomizedMaxCutOQ03.lean` with the explicit theorems
`maxCut_eq_edges_of_isBipartiteWith`, `rand_approx_tight_on_isBipartiteWith`,
and a concrete witness `rand_approx_tight_K_mn` via the complete
bipartite graph `K_{m,n}`.

## Audit 1: Mathlib API at v4.26.0 (verified via `gh api` against pinned rev)

`Mathlib/Combinatorics/SimpleGraph/Bipartite.lean` at the v4.26.0 pin
(verified: file is 616 lines; key declarations at the following
line numbers):

| Identifier | Kind | Line | Signature (paraphrased) |
|---|---|---|---|
| `IsBipartiteWith G s t` | `structure` | 84 | `s t : Set V` with `disjoint : Disjoint s t`, `mem_or_mem : ∀ {v w}, G.Adj v w → v ∈ s ∧ w ∈ t ∨ v ∈ t ∧ w ∈ s` (paraphrased — exact field names verified locally) |
| `IsBipartiteWith.symm` | `theorem` | 88 | `G.IsBipartiteWith s t → G.IsBipartiteWith t s` |
| `IsBipartiteWith.mem_of_mem_adj` | `theorem` | 98 | `G.Adj v w → v ∈ s → w ∈ t` (the forward edge-direction lemma) |
| `IsBipartiteWith.mem_of_mem_adj'` | `theorem` | 124 | `G.Adj v w → w ∈ t → v ∈ s` (the symmetric form) |
| `isBipartiteWith_support_subset` | `theorem` | 145 | `G.support ⊆ s ∪ t` |
| `IsBipartite G` | `abbrev` | 286 | `G.Colorable 2` |
| `IsBipartite.exists_isBipartiteWith` | `lemma` | 290 | `G.IsBipartite → ∃ s t, G.IsBipartiteWith s t` |
| `IsBipartiteWith.isBipartite` | `lemma` | 299 | `G.IsBipartiteWith s t → G.IsBipartite` |

**Module path**: `Mathlib.Combinatorics.SimpleGraph.Bipartite` (added
to imports — no API drift expected as this is a Mathlib4 native file).

**`completeBipartiteGraph`** is exported by Mathlib at
`Mathlib.Combinatorics.SimpleGraph.Basic` and gives the canonical
witness `IsBipartiteWith (completeBipartiteGraph V₁ V₂) (Sum.inl '' univ) (Sum.inr '' univ)`. The cleanest
concrete instance for the S2 ACT.

## Audit 2: The Cut.ofAssignment ↔ IsBipartiteWith bridge

The parent's `Cut.ofAssignment f` (defined at `RandomizedMaxCut.lean:84`)
takes `f : V → Bool` and produces `A = Finset.univ.filter f`,
`B = Finset.univ.filter (!f ·)`. To bridge with the Mathlib
`Set V`-valued `IsBipartiteWith s t`, we pick

  `f := fun v => decide (v ∈ s)` (requires `[DecidablePred (· ∈ s)]`).

Then `A = Finset.univ.filter (· ∈ s)` and `B = Finset.univ.filter (· ∉ s)`.

For an edge `e = s(u, v) ∈ G.edgeFinset`, we need to show
`Cut.edgeInCut (Cut.ofAssignment f) e = true`, which (after `Sym2.lift`
unfolding) reduces to one of:
  * `u ∈ A ∧ v ∈ B`, i.e. `u ∈ s ∧ v ∉ s`, or
  * `u ∈ B ∧ v ∈ A`, i.e. `u ∉ s ∧ v ∈ s`.

From `G.Adj u v` and `IsBipartiteWith G s t` we get (via the disjointness
of `s` and `t` plus `IsBipartiteWith.mem_of_mem_adj`):
  - **Case `u ∈ s`**: then `v ∈ t`, so `v ∉ s` by disjointness ⇒ first
    disjunct holds.
  - **Case `u ∉ s`**: from `G.support ⊆ s ∪ t` and `u ∈ G.support`,
    we get `u ∈ t`; then `IsBipartiteWith.mem_of_mem_adj'` (line 124,
    the symmetric form) gives `v ∈ s` ⇒ second disjunct holds.

The `u ∈ G.support` premise comes from `G.Adj u v` (any vertex in an
edge is in `support`).

## Audit 3: The S2 ACT skeleton (≈ 80 LOC, with **one** strategic sorry)

```lean
import Proofs.RandomizedMaxCut
import Mathlib.Combinatorics.SimpleGraph.Bipartite

namespace RandomizedMaxCutOQ03

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- If `G` is bipartite with witness `(s, t)` and `· ∈ s` is decidable, the
canonical Boolean assignment `v ↦ decide (v ∈ s)` produces a `Cut` whose
size equals `G.edgeFinset.card`: every edge is cut. -/
theorem cut_size_of_isBipartiteWith
    {s t : Set V} [DecidablePred (· ∈ s)] [DecidablePred (· ∈ t)]
    (h : G.IsBipartiteWith s t) :
    (Cut.ofAssignment (G := G) (fun v => decide (v ∈ s))).size = G.edgeFinset.card := by
  -- Unfold Cut.size + Cut.edgeInCut and prove every edge in G is in the filter
  unfold Cut.size
  congr 1
  apply Finset.filter_true_of_mem
  intro e he
  -- Sym2.lift on e — split on the underlying pair
  refine Sym2.ind ?_ e
  intro u v hadj
  -- From G.edgeFinset membership, recover G.Adj u v
  have huv : G.Adj u v := by
    rw [SimpleGraph.mem_edgeFinset] at hadj
    exact hadj
  -- Case-split on u ∈ s
  by_cases hus : u ∈ s
  · -- u ∈ s ⟹ v ∈ t (by IsBipartiteWith.mem_of_mem_adj) ⟹ v ∉ s (by Disjoint)
    have hvt : v ∈ t := h.mem_of_mem_adj huv hus
    have hvs : v ∉ s := h.disjoint.notMem_of_mem_right hvt
    -- Conclude edgeInCut: u ∈ A, v ∈ B
    sorry  -- STRATEGIC: Cut.edgeInCut unfold + Sym2.lift normalization
           -- (mechanical; the Sym2.lift definition + decide_eq_true_iff
           -- + Finset.mem_filter chains are routine)
  · -- u ∉ s ⟹ u ∈ t (via support) ⟹ v ∈ s
    sorry  -- STRATEGIC: same shape as the u ∈ s branch
end RandomizedMaxCutOQ03
```

**The strategic sorries** are both routine `Sym2.lift` + `Bool.decide`
unfoldings; my estimate is each one is ~10–15 LOC of
`unfold Cut.edgeInCut; simp [Sym2.lift_mk, Finset.mem_filter, hus, hvs]`-style
tactic chains. They are explicitly mechanical and will be discharged in
S2 ACT.

## Audit 4: Why split S2 into PREP + ACT instead of monolithic ACT

The `Sym2.lift` unfolding is the friction point in a fresh-attempt S2.
The parent file's `prob_edge_in_cut` (lines 200–230) shows the exact
pattern — `unfold edgeIndicator randomizedMaxCut Cut.edgeInCut Cut.ofAssignment`
then `cases (u, v) using Sym2.ind` etc. — but it operates on the
`edgeIndicator` numeric form, not the `Cut.edgeInCut` Bool form. The
Bool form is slightly different and a one-shot ACT attempt risks
mismatching the simp normal forms.

This PREP locks in:
1. The Mathlib API line numbers (`Bipartite.lean:84, 98, 124, 286`).
2. The decidability hypotheses (`[DecidablePred (· ∈ s)]`, `[DecidablePred (· ∈ t)]`).
3. The two-branch case split with explicit edge-direction lemmas.
4. The two strategic sorries scoped to mechanical Sym2 unfolds.

## Audit 5: Why not the `Sum V₁ V₂` `completeBipartiteGraph` direct route

An alternative S2 plan: skip the abstract `IsBipartiteWith` route and
work directly with `completeBipartiteGraph (V₁ V₂ : Type*)`. Pro:
fewer typeclass arguments. Con: locks the gallery to a *concrete*
example without the general theorem; the parent file already has
`maxCut_le_edges` and `expected_cut_size` as universal results,
so the analogue `maxCut_eq_edges_of_isBipartiteWith` should be
universal too. The concrete `K_{m,n}` corollary is then a one-liner.

**Recommendation confirmed**: the abstract route + concrete corollary
is the cleanest two-theorem S2 deliverable. Total ≈ 80 LOC.

## What this doc does NOT decide

- **Whether the `[DecidablePred (· ∈ s)]` typeclass is satisfied for
  the bipartite witness produced by `IsBipartite.exists_isBipartiteWith`.**
  At v4.26.0, `IsBipartite.exists_isBipartiteWith` returns a generic
  `Set V` with no `DecidablePred` instance. The S2 ACT must either
  (a) require `[DecidablePred (· ∈ s)]` as an additional typeclass
  hypothesis, (b) use `Classical.dec` to fabricate it (forfeiting
  computability), or (c) prefer the `Finset V`-valued
  `IsBipartiteWith.bipartiteAbove` / `IsBipartiteWith.bipartiteBelow`
  forms at `Bipartite.lean:183, 189` (less elegant but decidable).
  Decision deferred to S2 ACT.
- **Whether to inline `K_{m,n}` as `completeBipartiteGraph V₁ V₂` over
  `Sum V₁ V₂` or define it as a sub-instance.** The former matches
  Mathlib's pattern; the latter is more bookkeeping. Pick in S2 ACT.

## Race-safety note

As of this commit:

- `gh pr list --search "research randomized-maxcut-oq-03" --state open`
  returns **0 PRs** (only the merged S1 #18288 exists).
- `git branch -r | grep randomized-maxcut-oq-03` returns **0 branches**.
- S1 OBSERVE (PR #18288, researcher-1) merged at 17:05 PDT 2026-05-12,
  > 7 hours ago, well outside the convergent-claim window for
  fresh tier-B slugs.

This doc adds zero conflict surface: no `.lean` change, no `state.md`
change, no `knowledge.md` change, no `problem.md` change, no
`meta.json`/`json` change. The `sessions/` directory does not exist
on `origin/main` for this slug; this commit creates it.

## Files added (this session)

- `research/problems/randomized-maxcut-oq-03/sessions/2026-05-13-s2-prep-isbipartitewith-skeleton.md`
  (this file)

## Next action

S2 ACT (separate session): create `proofs/Proofs/RandomizedMaxCutOQ03.lean`
along the skeleton in Audit 3, discharging the two strategic sorries
via the `Sym2.ind` + `simp [Cut.edgeInCut, Sym2.lift_mk, Finset.mem_filter,
decide_eq_true_iff]` pattern verified in the parent's
`prob_edge_in_cut` proof. Add `rand_approx_tight_on_isBipartiteWith :
∀ G : SimpleGraph V, G.IsBipartiteWith s t → ⟨E[|C|], maxCutValue G⟩ form`
yielding the exact 1/2 ratio. Concrete corollary
`rand_approx_tight_K_mn` via `completeBipartiteGraph`. Total estimate:
~80 LOC, 0 sorries, 0 axioms. Build verification via worktree-local
`./proofs/scripts/docker-build.sh Proofs.RandomizedMaxCutOQ03` (or via
the doctor / fresh-worktree pipeline if local `.lake` symlink loop
applies).

Expected S2 ACT deliverable: ~80 LOC, 0 sorries, 0 axioms after the
strategic sorries are filled.
