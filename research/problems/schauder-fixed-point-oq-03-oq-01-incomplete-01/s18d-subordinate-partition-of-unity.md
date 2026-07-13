# S18d — Subordinate Partition of Unity (Cellina–Browder Step 3)

**Date:** 2026-05-12
**Researcher:** researcher-12
**Iteration:** S18d (sixth scaffold step in the Cellina–Browder
`approx_selection_exists` axiom-elimination decomposition)
**Status:** Build pending (Mathlib pin `2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`,
v4.26.0)

## Goal

Add the third Cellina–Browder scaffold step to
`Proofs/SchauderFixedPointOQ03OQ01.lean`: package the S18c open cover
`U : ↥S → Set ↥S` together with a *partition of unity subordinate to
it*. The subordinate partition `ρ : PartitionOfUnity (↥S) (↥S) Set.univ`
is the centerpiece of the Cellina–Browder construction; in S18e the
continuous selection
`f x := ∑ᶠ i, ρ i x • y_i` (with `y_i ∈ F i`) inherits its continuity
from `ρ`'s smoothness and its `ε`-graph-approximation property from
`ρ.IsSubordinate U` plus S18c's
`F z ⊆ Metric.thickening ε (F x)` clause.

## Mathlib API used

- `PartitionOfUnity.exists_isSubordinate` (`Mathlib.Topology.PartitionOfUnity`
  line 629 at the pinned rev). Signature:

  ```
  theorem exists_isSubordinate [NormalSpace X] [ParacompactSpace X]
      (hs : IsClosed s) (U : ι → Set X)
      (ho : ∀ i, IsOpen (U i)) (hU : s ⊆ ⋃ i, U i) :
      ∃ f : PartitionOfUnity ι X s, f.IsSubordinate U
  ```

- The required `[NormalSpace ↥S]` and `[ParacompactSpace ↥S]` instances
  are supplied automatically by the `haveI : CompactSpace ↥S` line plus
  Mathlib's typeclass derivation chain documented in
  `typeclass_witnesses_compact_subset` (S18b, PR #17802):
  - `NormalSpace ↥S` ← `CompactSpace + R1Space ← T2Space (Subtype.t2Space)`
  - `ParacompactSpace ↥S` ← `paracompact_of_compact`

- The closed target set is taken to be `Set.univ`, with `IsClosed Set.univ`
  discharged by `isClosed_univ`. The cover hypothesis
  `Set.univ ⊆ ⋃ x : ↥S, U x` is derived from S18c's basepoint condition
  `x ∈ U x` via `Set.mem_iUnion.mpr ⟨x, hU_mem x⟩`.

## Lemma signature

```
private lemma exists_partition_subordinate_to_uhc_cover {n : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS_compact : IsCompact S)
    (F : SetValuedMap (↥S) (↥S))
    (hF_uhc : IsUpperHemicontinuous F)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ U : ↥S → Set ↥S,
      ∃ ρ : PartitionOfUnity (↥S) (↥S) (Set.univ : Set ↥S),
        (∀ x : ↥S, IsOpen (U x)) ∧
        (∀ x : ↥S, x ∈ U x) ∧
        (∀ x z : ↥S, z ∈ U x → F z ⊆ Metric.thickening ε (F x)) ∧
        ρ.IsSubordinate U
```

Located immediately after `exists_finite_subcover_for_uhc` (Step 2,
S18c). The proof body is ~10 lines; the surrounding docstring spells
out where each ingredient comes from so the eventual S18e selection
construction can locate the lemma without re-reading the S17 survey.

## Indexing choice (full ↥S vs S18c finite subfamily)

The lemma returns the *full* ↥S-indexed partition of unity rather than
the finite one indexed by S18c's `s : Finset ↥S`. Two reasons:

1. `PartitionOfUnity` over a finite index requires
   `[Fintype (Subtype (· ∈ s))]` plumbing that `exists_isSubordinate`
   does not expect; the Mathlib API expects an arbitrary index `ι : Type`.
2. The local-finiteness clause inherited from
   `BumpCovering.exists_isSubordinate` ensures that at every point only
   finitely many `ρ i x` are nonzero, recovering the finite-sum behavior
   needed for S18e's continuous selection
   `f x := ∑ᶠ i, ρ i x • y_i` (cf. `convex_combination_of_partition_in_S`,
   S18a, PR #17755).

The S18c `s : Finset ↥S` and `⋃ x ∈ s, U x = ⊤` clauses are accordingly
discarded (`_s` / `_hs_cover` placeholders) — they remain available
in `exists_finite_subcover_for_uhc` for any S18e variant that prefers
a finite index.

## Net file change

- Added one private lemma (`exists_partition_subordinate_to_uhc_cover`).
- File: `Proofs/SchauderFixedPointOQ03OQ01.lean` 957 → 1015 lines (+58).
- meta.json: `lineCount` 957 → 1015, `theoremCount` 9 → 10 (inner
  `leanFile` block); outer `formalization` block synced to 1015 / 10.
- Axiom count unchanged at 2 (`brouwer_unit_ball`, `approx_selection_exists`).
- Sorry count unchanged at 0.

## Build status

Not built locally (Docker memory cap; matches the S25–S31 ballot,
S18b/S18c precedent of "(build pending)" merges for scaffold-only PRs
with new private helpers using directly-fetched Mathlib API at the
pinned rev). The `PartitionOfUnity.exists_isSubordinate` signature was
verified by directly downloading
`Mathlib/Topology/PartitionOfUnity.lean` at rev
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67` (line 629) via
`raw.githubusercontent.com`; all argument types match the call site.

## Next action (S18e, ~60–80 lines)

Define the continuous selection `f : C(↥S, ↥S)` (Cellina Step 4):

1. Choose representatives `y : ↥S → ↥S` with `y x ∈ F x`
   (`choose y hy using fun x => hF_ne x`, where `hF_ne` is the
   `∀ x, (F x).Nonempty` hypothesis carried through
   `kakutani_from_brouwer`).
2. Define `f x := ∑ᶠ i, ρ i x • (y i : EuclideanSpace ℝ (Fin n))`,
   then return to `↥S` using `Convex.sum_mem` (already abstracted as
   `convex_combination_of_partition_in_S`, S18a) plus the `hF_convex`
   clause from `kakutani_from_brouwer`.
3. Continuity follows from `ρ.continuous_smul_finsum` (or its
   subfamily-restricted variant; check `Mathlib.Topology.PartitionOfUnity`
   for the exact lemma name at the pinned rev).

The `ε`-graph-approximation property is then S18f.
