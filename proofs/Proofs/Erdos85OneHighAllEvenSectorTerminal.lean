import Proofs.Erdos85OneHighStructuralTerminalInterface
import Proofs.Erdos85OneHighExchangedMissCounting

/-! # Reduction of the one-high all-even terminal -/

namespace Erdos85

noncomputable section

/-- If every exchanged key has even multiplicity, then the total number of
nonconstant matching edges is even. -/
theorem even_nonconstantMatchingEdgeSources_of_all_exchanged_even
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L)
    (heven : ∀ key ∈ exchangedMissPairKeys L,
      Even (exchangedMissPairMultiplicity mate label key)) :
    Even (nonconstantMatchingEdgeSources mate label).card := by
  rw [← sum_exchangedMissPairMultiplicity_over_keys mate label]
  exact Finset.even_sum _ fun key hkey => heven key hkey

/-- Matching edges on which the two endpoint miss labels agree. -/
def constantMatchingEdgeSources
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [DecidableEq L] (mate : X → X) (label : X → L) : Finset X :=
  (matchingEdgeSources mate).filter fun x => label x = label (mate x)

theorem card_nonconstant_add_card_constantMatchingEdgeSources
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [DecidableEq L] (mate : X → X) (label : X → L) :
    (nonconstantMatchingEdgeSources mate label).card +
      (constantMatchingEdgeSources mate label).card =
        (matchingEdgeSources mate).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [nonconstantMatchingEdgeSources, constantMatchingEdgeSources,
      matchingEdgeSources, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hlabel : label x = label (mate x) <;> simp [hlabel]
  · rw [Finset.disjoint_left]
    intro x hxNon hxConst
    exact (Finset.mem_filter.mp hxNon).2.2
      (Finset.mem_filter.mp hxConst).2

/-- The raw one-high profile has exactly `16 - profile` internal matching
edges across its eight five-point branches. -/
theorem card_globalMatchingEdgeSources_eq_profile
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (p : OneHighRawV2Presentation G hfree v) :
    (matchingEdgeSources (oneHighGlobalInternalMate G hfree v)).card =
      16 - p.profile := by
  have hcard := card_oneHighAllMatchedVertices_eq_profile
    G v p.branchLabel p.profile p.profile_le p.matched_count
  have htwice := two_mul_matchingEdgeSources_card
    (oneHighGlobalInternalMate G hfree v)
    (oneHighGlobalInternalMate_involutive G hfree v)
    (oneHighGlobalInternalMate_ne G hfree v)
  rw [hcard] at htwice
  omega

private theorem even_sixteen_sub_iff (a : Nat) (ha : a ≤ 4) :
    Even (16 - a) ↔ Even a := by
  interval_cases a <;> decide

/-- Exact all-even invariant: same-miss internal edges have the same parity
as the family profile.  Thus the five terminal profiles require respectively
an even, odd, even, odd, and even same-miss count. -/
theorem even_constantMatchingEdgeSources_iff_profile_even_of_all_exchanged_even
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (heven : ∀ key ∈ exchangedMissPairKeys (Fin 8),
      Even (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)) key)) :
    Even (constantMatchingEdgeSources
      (oneHighGlobalInternalMate G hfree v)
      (fun x => p.branchLabel
        (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
          p.mate p.mate_adj x))).card ↔ Even p.profile := by
  let mate := oneHighGlobalInternalMate G hfree v
  let label := fun x => p.branchLabel
    (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
      p.mate p.mate_adj x)
  have hnon : Even (nonconstantMatchingEdgeSources mate label).card :=
    even_nonconstantMatchingEdgeSources_of_all_exchanged_even mate label heven
  have hsum := card_nonconstant_add_card_constantMatchingEdgeSources mate label
  have htotal := card_globalMatchingEdgeSources_eq_profile G hfree p
  dsimp only [mate] at hsum htotal
  rw [htotal] at hsum
  constructor
  · intro hconst
    apply (even_sixteen_sub_iff p.profile p.profile_le).mp
    rw [← hsum]
    exact hnon.add hconst
  · intro hprofile
    have htotalEven : Even (16 - p.profile) :=
      (even_sixteen_sub_iff p.profile p.profile_le).mpr hprofile
    rw [← hsum, Nat.even_add] at htotalEven
    exact htotalEven.mp hnon

/-- The all-even terminal is reduced to the graph-side assertion that the
global nonconstant matching-edge count is odd. -/
theorem oneHighAllEvenSectorExcluded_of_global_nonconstant_odd
    (hodd : ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
      (_ : DecidableRel (antipodalGraph G).Adj)
      (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
      (hfree : ¬ containsC4 (Fin 49) G) →
      (hmin : ∀ x : Fin 49, 7 ≤ G.degree x) →
      (hHigh : (orderFortyNineHighVertices G).card = 1) →
      ∀ {v : Fin 49} (hv : G.degree v = 8)
        (p : OneHighRawV2Presentation G hfree v),
        Odd (nonconstantMatchingEdgeSources
          (oneHighGlobalInternalMate G hfree v)
          (fun x => p.branchLabel
            (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
              p.mate p.mate_adj x))).card) :
    OneHighAllEvenSectorExcluded := by
  intro G _ _ _ hfree hmin hHigh v hv p
  dsimp only
  intro heven
  let mate := oneHighGlobalInternalMate G hfree v
  let label := fun x => p.branchLabel
    (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
      p.mate p.mate_adj x)
  have hcardEven : Even (nonconstantMatchingEdgeSources mate label).card :=
    even_nonconstantMatchingEdgeSources_of_all_exchanged_even mate label heven
  have hcardOdd : Odd (nonconstantMatchingEdgeSources mate label).card :=
    hodd G inferInstance inferInstance inferInstance hfree hmin hHigh hv p
  exact (Nat.not_even_iff_odd.mpr hcardOdd) hcardEven

end

end Erdos85
