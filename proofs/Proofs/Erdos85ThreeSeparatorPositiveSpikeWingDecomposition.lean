import Proofs.Erdos85ThreeSeparatorPositiveSpikeNeighborhoodExhaustion

/-! # Wing decomposition in the positive-spike three-separator profile -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- A point with exactly one neighbor in `W` belongs to a unique pole wing. -/
theorem existsUnique_adj_of_neighborFinset_inter_card_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (z : V) (W : Finset V)
    (hcard : (G.neighborFinset z ∩ W).card = 1) :
    ∃! w, w ∈ W ∧ G.Adj z w := by
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
  refine ⟨w, ?_, ?_⟩
  · have hmem : w ∈ G.neighborFinset z ∩ W := by rw [hw]; simp
    refine ⟨(Finset.mem_inter.mp hmem).2, ?_⟩
    simpa [SimpleGraph.mem_neighborFinset] using (Finset.mem_inter.mp hmem).1
  · intro u hu
    have humem : u ∈ G.neighborFinset z ∩ W := by
      simpa [SimpleGraph.mem_neighborFinset] using ⟨hu.2, hu.1⟩
    rw [hw] at humem
    exact Finset.mem_singleton.mp humem

/-- Removing the three overlap points and the spike center leaves disjoint
one-neighbor wings on both profile sets; their per-pole cardinalities are
the pole loads minus the two overlap incidences. -/
theorem positiveSpike_threeSeparator_wing_decomposition
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ}
    (hreg : ∀ v, G.degree v = q)
    (W K R : Finset V) (c : V)
    (hWcard : W.card = 3) (hKRcard : (K ∩ R).card = 3)
    (hcK : c ∈ K) (hcR : c ∉ R)
    (hprofile : ∀ v,
      ((G.neighborFinset v ∩ W).card : ℤ) =
        (if v ∈ K then 1 else 0) + (if v ∈ R then 1 else 0) -
          (if v = c then 1 else 0))
    (hpoleLoad : ∀ w ∈ W,
      (G.neighborFinset w ∩ K).card +
        (G.neighborFinset w ∩ R).card = q + 2) :
    (∀ z ∈ K \ ((K ∩ R) ∪ {c}), ∃! w, w ∈ W ∧ G.Adj z w) ∧
      (∀ z ∈ R \ (K ∩ R), ∃! w, w ∈ W ∧ G.Adj z w) ∧
      (∀ w ∈ W,
        (G.neighborFinset w ∩ (K \ ((K ∩ R) ∪ {c}))).card + 2 =
          (G.neighborFinset w ∩ K).card) ∧
      ∀ w ∈ W,
        (G.neighborFinset w ∩ (R \ (K ∩ R))).card + 2 =
          (G.neighborFinset w ∩ R).card := by
  let P := K ∩ R
  have htwo := (positiveSpike_threeSeparator_overlap_is_two_regular
    G hreg W K R c hWcard hKRcard hcK hcR hprofile hpoleLoad).2
  have hcZero : (G.neighborFinset c ∩ W).card = 0 := by
    have h : ((G.neighborFinset c ∩ W).card : ℤ) = 0 := by
      simpa [hcK, hcR] using hprofile c
    exact Int.ofNat_eq_zero.mp h
  have hcNotAdj : ∀ w ∈ W, ¬ G.Adj w c := by
    intro w hw hadj
    have : w ∈ G.neighborFinset c ∩ W := by
      simp [SimpleGraph.mem_neighborFinset, hw, (G.adj_comm w c).mp hadj]
    simpa [Finset.card_eq_zero.mp hcZero] using this
  have hKunique : ∀ z ∈ K \ (P ∪ {c}), ∃! w, w ∈ W ∧ G.Adj z w := by
    intro z hz
    have hzK := (Finset.mem_sdiff.mp hz).1
    have hzout := (Finset.mem_sdiff.mp hz).2
    have hzR : z ∉ R := by
      intro hzR
      exact hzout (Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hzK, hzR⟩))
    have hzc : z ≠ c := by
      intro hzc
      exact hzout (Finset.mem_union_right _ (by simp [hzc]))
    apply existsUnique_adj_of_neighborFinset_inter_card_one G z W
    have h := hprofile z
    simp [hzK, hzR, hzc] at h
    exact_mod_cast h
  have hRunique : ∀ z ∈ R \ P, ∃! w, w ∈ W ∧ G.Adj z w := by
    intro z hz
    have hzR := (Finset.mem_sdiff.mp hz).1
    have hzout := (Finset.mem_sdiff.mp hz).2
    have hzK : z ∉ K := by
      intro hzK
      exact hzout (Finset.mem_inter.mpr ⟨hzK, hzR⟩)
    have hzc : z ≠ c := by
      intro hzc
      exact hcR (hzc ▸ hzR)
    apply existsUnique_adj_of_neighborFinset_inter_card_one G z W
    have h := hprofile z
    simp [hzK, hzR, hzc] at h
    exact_mod_cast h
  refine ⟨by simpa [P] using hKunique, by simpa [P] using hRunique, ?_, ?_⟩
  · intro w hw
    change (G.neighborFinset w ∩ (K \ (P ∪ {c}))).card + 2 =
      (G.neighborFinset w ∩ K).card
    have hdecomp :
        (G.neighborFinset w ∩ K) =
          (G.neighborFinset w ∩ P) ∪
            (G.neighborFinset w ∩ (K \ (P ∪ {c}))) := by
      ext z
      by_cases hzc : z = c
      · subst z
        simp [P, hcK, hcR, hcNotAdj w hw]
      · simp [P, hzc]
        tauto
    have hdisj : Disjoint (G.neighborFinset w ∩ P)
        (G.neighborFinset w ∩ (K \ (P ∪ {c}))) := by
      rw [Finset.disjoint_left]
      intro z hzP hzWing
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hzWing).2).2
        (Finset.mem_union_left _ (Finset.mem_inter.mp hzP).2)
    rw [hdecomp, Finset.card_union_of_disjoint hdisj, htwo w hw]
    omega
  · intro w hw
    change (G.neighborFinset w ∩ (R \ P)).card + 2 =
      (G.neighborFinset w ∩ R).card
    have hdecomp :
        (G.neighborFinset w ∩ R) =
          (G.neighborFinset w ∩ P) ∪
            (G.neighborFinset w ∩ (R \ P)) := by
      ext z
      simp [P]
      tauto
    have hdisj : Disjoint (G.neighborFinset w ∩ P)
        (G.neighborFinset w ∩ (R \ P)) := by
      rw [Finset.disjoint_left]
      intro z hzP hzWing
      exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hzWing).2).2
        (Finset.mem_inter.mp hzP).2
    rw [hdecomp, Finset.card_union_of_disjoint hdisj, htwo w hw]
    omega

#print axioms existsUnique_adj_of_neighborFinset_inter_card_one
#print axioms positiveSpike_threeSeparator_wing_decomposition

end

end Erdos85
