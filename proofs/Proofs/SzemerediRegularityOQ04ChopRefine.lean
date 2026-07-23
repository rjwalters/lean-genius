/-
# Szemerédi Regularity (OQ-04): chop-refinement with full energy retention

First rung of the **re-equitization** residual (the single remaining obligation of
the OQ-04 two-level AFKS program): upgrade the bare-split successor partition to an
equitable one without losing the energy gain.  Re-equitization has two halves:

1. **Refinement half (this file):** chop every block of a partition family into
   pieces of size exactly `m` plus at most ONE remainder piece (of size `< m`) per
   block.  The result *refines* the family, so by the full simultaneous refinement
   monotonicity (`partitionEnergy_refine_mono`, FullRefine) it retains **all** of the
   partition energy — no `δ`-fraction loss at this stage.  The number of deficient
   pieces is bounded by the number of blocks, which is exactly the mass-control
   input the merging half needs.
2. **Merging half (still open):** pool the `≤ |P|` deficient remainders and re-cut
   them into size-`m` chunks.  This step is NOT a refinement; its energy loss must
   be bounded by the small total mass of the pooled set.  Deep; not attempted here.

## What this file proves (0 axioms, 0 sorries)

* `exists_chop_pieces` — single-block chopping engine: every finite set `A` splits
  into a pairwise-disjoint family of nonempty pieces covering `A`, each of size
  `≤ m`, with **at most one** piece of size `< m` (all others exactly `m`).  Strong
  induction on `A`, peeling size-`m` subsets via `Finset.exists_subset_card_eq`.
* `exists_chop_refinement` — family-level capstone: every pairwise-disjoint family
  `P` admits a chopped refinement `Q` with
  - every piece contained in a block of `P` (refinement) and same union (cover),
  - `Q` pairwise disjoint, all pieces nonempty of size `≤ m`,
  - at most `P.card` pieces of size `< m` (the rest have size exactly `m`),
  - `partitionEnergy G P ≤ partitionEnergy G Q` — full energy retention.

Everything here is elementary bookkeeping plus `partitionEnergy_refine_mono`;
the analytic difficulty of re-equitization is concentrated entirely in the
merging half, which consumes the `≤ P.card` deficient-piece bound proved here.
-/
import Mathlib
import Proofs.SzemerediRegularityOQ04FullRefine

namespace Szemeredi.RegularityOQ04ChopRefine

open Szemeredi.Core Szemeredi.Regularity Szemeredi.RegularityOQ04Energy
open Szemeredi.RegularityOQ04Bridge Szemeredi.RegularityOQ04FamilySplit
open Szemeredi.RegularityOQ04FullRefine

variable {V : Type*} [Fintype V] [DecidableEq V]

-- ═══════════════════════════════════════════════════════════════════
-- PART I: SINGLE-BLOCK CHOPPING ENGINE
-- ═══════════════════════════════════════════════════════════════════

omit [Fintype V] in
/-- **Single-block chopping engine.**  Every finite set `A` splits into a
pairwise-disjoint family `F` of nonempty pieces covering `A`, each piece of size
at most `m`, with **at most one** deficient piece of size `< m` — so all other
pieces have size exactly `m`.  Proof: strong induction on `A`; while `m < |A|`
peel off a size-`m` subset (`Finset.exists_subset_card_eq`) and recurse on the
rest; the base block (of size `≤ m`) is the unique possible deficient piece. -/
theorem exists_chop_pieces (m : ℕ) (hm : 1 ≤ m) (A : Finset V) :
    ∃ F : Finset (Finset V),
      F.biUnion id = A ∧
      (↑F : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ c ∈ F, c.Nonempty) ∧
      (∀ c ∈ F, c.card ≤ m) ∧
      (F.filter (fun c => c.card < m)).card ≤ 1 := by
  classical
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases hA : A.card ≤ m
    · rcases Finset.eq_empty_or_nonempty A with rfl | hne
      · exact ⟨∅, by simp, by simp, by simp, by simp, by simp⟩
      · refine ⟨{A}, by simp, ?_, ?_, ?_, ?_⟩
        · rw [Finset.coe_singleton]
          exact Set.pairwiseDisjoint_singleton A id
        · intro c hc
          rw [Finset.mem_singleton] at hc
          subst hc; exact hne
        · intro c hc
          rw [Finset.mem_singleton] at hc
          subst hc; exact hA
        · exact le_trans (Finset.card_filter_le _ _) (by simp)
    · -- peel a size-`m` subset and recurse on the remainder
      have hAm : m < A.card := Nat.lt_of_not_le hA
      obtain ⟨S, hSsub, hScard⟩ := Finset.exists_subset_card_eq hAm.le
      have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
      have hss : A \ S ⊂ A := Finset.sdiff_ssubset hSsub hSne
      obtain ⟨F', hcov', hdisj', hne', hcard', hfilter'⟩ := ih (A \ S) hss
      -- every recursive piece avoids `S`
      have hsub' : ∀ c ∈ F', c ⊆ A \ S := by
        intro c hc
        calc c = id c := rfl
          _ ⊆ F'.biUnion id := Finset.subset_biUnion_of_mem id hc
          _ = A \ S := hcov'
      have hSdisj : ∀ c ∈ F', Disjoint S c := by
        intro c hc
        exact (Finset.sdiff_disjoint.mono_left (hsub' c hc)).symm
      refine ⟨insert S F', ?_, ?_, ?_, ?_, ?_⟩
      · rw [Finset.biUnion_insert, hcov']
        exact Finset.union_sdiff_of_subset hSsub
      · rw [Finset.coe_insert, Set.pairwiseDisjoint_insert]
        exact ⟨hdisj', fun c hc _ => hSdisj c (Finset.mem_coe.mp hc)⟩
      · intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hc'
        · exact hSne
        · exact hne' c hc'
      · intro c hc
        rcases Finset.mem_insert.mp hc with rfl | hc'
        · exact hScard.le
        · exact hcard' c hc'
      · rw [Finset.filter_insert, if_neg (by omega)]
        exact hfilter'

-- ═══════════════════════════════════════════════════════════════════
-- PART II: FAMILY-LEVEL CHOP-REFINEMENT WITH FULL ENERGY RETENTION
-- ═══════════════════════════════════════════════════════════════════

/-- **Chop-refinement of a partition family, retaining all energy.**  Every
pairwise-disjoint family `P` admits a refinement `Q` (every piece inside a block,
same union) that is pairwise disjoint with all pieces nonempty of size `≤ m`, at
most `P.card` pieces of size `< m` (all others exactly size `m`), and
`partitionEnergy G P ≤ partitionEnergy G Q`.

This is the refinement half of re-equitization: since `Q` genuinely refines `P`,
`partitionEnergy_refine_mono` applies and NO fraction of the energy gain is lost.
The still-open merging half must absorb the `≤ P.card` deficient pieces into
size-`m` chunks at a controlled energy cost. -/
theorem exists_chop_refinement (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : ℕ) (hm : 1 ≤ m) (P : Finset (Finset V))
    (hdisj : (↑P : Set (Finset V)).PairwiseDisjoint id) :
    ∃ Q : Finset (Finset V),
      (∀ c ∈ Q, ∃ A ∈ P, c ⊆ A) ∧
      Q.biUnion id = P.biUnion id ∧
      (↑Q : Set (Finset V)).PairwiseDisjoint id ∧
      (∀ c ∈ Q, c.Nonempty) ∧
      (∀ c ∈ Q, c.card ≤ m) ∧
      (Q.filter (fun c => c.card < m)).card ≤ P.card ∧
      partitionEnergy G P ≤ partitionEnergy G Q := by
  classical
  -- choose a chopping of every block
  choose pieces hcov hdisjIn hne hcard hfilter using exists_chop_pieces (V := V) m hm
  -- pieces of a block stay inside it
  have hpiece_sub : ∀ A, ∀ c ∈ pieces A, c ⊆ A := by
    intro A c hc
    calc c = id c := rfl
      _ ⊆ (pieces A).biUnion id := Finset.subset_biUnion_of_mem id hc
      _ = A := hcov A
  -- distinct blocks receive disjoint piece-collections
  have hdisjOut : (↑P : Set (Finset V)).PairwiseDisjoint pieces := by
    intro A hA B hB hAB
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro c hcA hcB
    obtain ⟨x, hx⟩ := hne A c hcA
    have hxA : x ∈ A := hpiece_sub A c hcA hx
    have hxB : x ∈ B := hpiece_sub B c hcB hx
    exact Finset.disjoint_left.mp (hdisj hA hB hAB) hxA hxB
  refine ⟨P.biUnion pieces, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- refinement: every piece lies inside its parent block
    intro c hc
    obtain ⟨A, hA, hcA⟩ := Finset.mem_biUnion.mp hc
    exact ⟨A, hA, hpiece_sub A c hcA⟩
  · -- cover: the chopped family has the same union
    rw [Finset.biUnion_biUnion]
    exact Finset.biUnion_congr rfl (fun A _ => hcov A)
  · -- pairwise disjointness of all pieces
    intro c hc d hd hcd
    obtain ⟨A, hA, hcA⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hc)
    obtain ⟨B, hB, hdB⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hd)
    by_cases hAB : A = B
    · subst hAB
      exact hdisjIn A (Finset.mem_coe.mpr hcA) (Finset.mem_coe.mpr hdB) hcd
    · exact (hdisj hA hB hAB).mono (hpiece_sub A c hcA) (hpiece_sub B d hdB)
  · -- nonemptiness
    intro c hc
    obtain ⟨A, _, hcA⟩ := Finset.mem_biUnion.mp hc
    exact hne A c hcA
  · -- size ceiling
    intro c hc
    obtain ⟨A, _, hcA⟩ := Finset.mem_biUnion.mp hc
    exact hcard A c hcA
  · -- at most one deficient piece per block
    rw [Finset.filter_biUnion]
    calc (P.biUnion fun A => (pieces A).filter (fun c => c.card < m)).card
        ≤ ∑ A ∈ P, ((pieces A).filter (fun c => c.card < m)).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _A ∈ P, 1 := Finset.sum_le_sum (fun A _ => hfilter A)
      _ = P.card := by simp
  · -- full energy retention: `Q` refines `P`
    exact partitionEnergy_refine_mono G P pieces (fun A _ => hcov A)
      (fun A _ => hdisjIn A) hdisjOut

end Szemeredi.RegularityOQ04ChopRefine
