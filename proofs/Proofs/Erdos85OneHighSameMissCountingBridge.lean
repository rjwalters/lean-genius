import Proofs.Erdos85OneHighGlobalMissLabelCounting

/-! # Same-miss as vanishing of the nonconstant-edge count -/

namespace Erdos85

noncomputable section

/-- For a fixed-point-free involution, the oriented nonconstant-edge set is
empty exactly when the label is constant on every involution edge. -/
theorem nonconstantMatchingEdgeSources_eq_empty_iff
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [DecidableEq L]
    (mate : X → X) (label : X → L)
    (hinv : Function.Involutive mate) (hfree : ∀ x, mate x ≠ x) :
    nonconstantMatchingEdgeSources mate label = ∅ ↔
      ∀ x, label x = label (mate x) := by
  constructor
  · intro hempty x
    by_contra hlabel
    rcases lt_or_gt_of_ne (hfree x) with hmatex | hxmate
    · have hmateLt : mate x < mate (mate x) := by
        rw [hinv x]
        exact hmatex
      have hmateLabel : label (mate x) ≠ label (mate (mate x)) := by
        intro h
        apply hlabel
        rw [hinv x] at h
        exact h.symm
      have hx : mate x ∈ nonconstantMatchingEdgeSources mate label :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hmateLt, hmateLabel⟩
      rw [hempty] at hx
      simpa using hx
    · have hx : x ∈ nonconstantMatchingEdgeSources mate label :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxmate, hlabel⟩
      rw [hempty] at hx
      simpa using hx
  · intro hlabel
    ext x
    simp [nonconstantMatchingEdgeSources, hlabel x]

/-- Pointwise same-miss predicate on every global internal matching edge. -/
def OneHighGlobalSameMiss
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (v : V)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v}) : Prop :=
  ∀ x : OneHighAllMatchedVertices G v,
    ∀ u ∈ ((Finset.univ.erase x.1).erase (rootMate x.1)),
      ((G.neighborFinset x.2.1.1 ∩ secondLayerBranch G v u).card = 0 ↔
       (G.neighborFinset
          (oneHighGlobalInternalMate G hfree v x).2.1.1 ∩
            secondLayerBranch G v u).card = 0)

theorem oneHighGlobalMissLabel_eq_iff_sameMiss_at
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (x : OneHighAllMatchedVertices G v) :
    let mate := oneHighGlobalInternalMate G hfree v
    let label := oneHighGlobalMissLabel G hfree hv hexternal houterDegree
      rootMate hrootAdj
    label x = label (mate x) ↔
      ∀ u ∈ ((Finset.univ.erase x.1).erase (rootMate x.1)),
        ((G.neighborFinset x.2.1.1 ∩ secondLayerBranch G v u).card = 0 ↔
         (G.neighborFinset (mate x).2.1.1 ∩
            secondLayerBranch G v u).card = 0) := by
  dsimp
  let label := oneHighGlobalMissLabel G hfree hv hexternal houterDegree
    rootMate hrootAdj
  have hxMem := oneHighGlobalMissLabel_mem G hfree hv hexternal
    houterDegree rootMate hrootAdj x
  have hmMem := oneHighGlobalMissLabel_mem G hfree hv hexternal
    houterDegree rootMate hrootAdj
      (oneHighGlobalInternalMate G hfree v x)
  have hxSpec : label x ∈ ((Finset.univ.erase x.1).erase (rootMate x.1)) ∧
      (G.neighborFinset x.2.1.1 ∩
        secondLayerBranch G v (label x)).card = 0 := by
    simpa [label, oneHighFarMissBranches] using hxMem
  have hmSpec : label (oneHighGlobalInternalMate G hfree v x) ∈
        ((Finset.univ.erase x.1).erase (rootMate x.1)) ∧
      (G.neighborFinset
          (oneHighGlobalInternalMate G hfree v x).2.1.1 ∩
        secondLayerBranch G v
          (label (oneHighGlobalInternalMate G hfree v x))).card = 0 := by
    simpa [label, oneHighFarMissBranches, oneHighGlobalInternalMate] using hmMem
  have hxCard : (oneHighFarMissBranches G v rootMate x.1 x.2.1.1).card = 1 := by
    have hxMatched :
        (G.neighborFinset x.2.1.1 ∩ secondLayerBranch G v x.1).card = 1 := by
      rw [← degree_induce_secondLayerBranch_eq_card_inter]
      exact x.2.2
    exact card_oneHighFarMissBranches_eq_one_of_matched G hfree hv
      hexternal houterDegree rootMate hrootAdj x.1 x.2.1.1 x.2.1.2 hxMatched
  have hmCard : (oneHighFarMissBranches G v rootMate x.1
      (oneHighGlobalInternalMate G hfree v x).2.1.1).card = 1 := by
    have hmMatched :
        (G.neighborFinset
            (oneHighGlobalInternalMate G hfree v x).2.1.1 ∩
          secondLayerBranch G v x.1).card = 1 := by
      change (G.neighborFinset
          (oneHighInternalMate G hfree v x.1 x.2).1.1 ∩
        secondLayerBranch G v x.1).card = 1
      rw [← degree_induce_secondLayerBranch_eq_card_inter]
      exact (oneHighGlobalInternalMate G hfree v x).2.2
    exact card_oneHighFarMissBranches_eq_one_of_matched G hfree hv
      hexternal houterDegree rootMate hrootAdj x.1
      (oneHighGlobalInternalMate G hfree v x).2.1.1
      (oneHighGlobalInternalMate G hfree v x).2.1.2 hmMatched
  apply farMiss_iff_agree_of_unique G x.1 (rootMate x.1) hxSpec hmSpec
  · intro u hu
    have huMem : u ∈ oneHighFarMissBranches G v rootMate x.1 x.2.1.1 := by
      simpa [oneHighFarMissBranches] using hu
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hxCard
    rw [hz] at huMem hxMem
    have huEq : u = z := by simpa using huMem
    have hxEq : label x = z := by simpa using hxMem
    exact huEq.trans hxEq.symm
  · intro u hu
    have huMem : u ∈ oneHighFarMissBranches G v rootMate x.1
        (oneHighGlobalInternalMate G hfree v x).2.1.1 := by
      simpa [oneHighFarMissBranches] using hu
    have hmMem' : label (oneHighGlobalInternalMate G hfree v x) ∈
        oneHighFarMissBranches G v rootMate x.1
          (oneHighGlobalInternalMate G hfree v x).2.1.1 := by
      simpa [label, oneHighGlobalInternalMate] using hmMem
    obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hmCard
    rw [hz] at huMem hmMem'
    have huEq : u = z := by simpa using huMem
    have hmEq : label (oneHighGlobalInternalMate G hfree v x) = z := by
      simpa using hmMem'
    exact huEq.trans hmEq.symm

/-- The global nonconstant-edge count vanishes exactly at the same-miss
hypothesis used by the parity bridge. -/
theorem oneHigh_nonconstantSources_eq_empty_iff_globalSameMiss
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1) :
    let mate := oneHighGlobalInternalMate G hfree v
    let label := oneHighGlobalMissLabel G hfree hv hexternal houterDegree
      rootMate hrootAdj
    nonconstantMatchingEdgeSources mate label = ∅ ↔
      OneHighGlobalSameMiss G hfree v rootMate := by
  dsimp
  rw [nonconstantMatchingEdgeSources_eq_empty_iff _ _
    (oneHighGlobalInternalMate_involutive G hfree v)
    (oneHighGlobalInternalMate_ne G hfree v)]
  constructor
  · intro hlabel x
    exact (oneHighGlobalMissLabel_eq_iff_sameMiss_at G hfree hv hexternal
      houterDegree rootMate hrootAdj x).mp (hlabel x)
  · intro hsame x
    exact (oneHighGlobalMissLabel_eq_iff_sameMiss_at G hfree hv hexternal
      houterDegree rootMate hrootAdj x).mpr (hsame x)

end

end Erdos85
