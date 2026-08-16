import Proofs.Erdos85OneHighTwoEdgeMissMultiplicity
import Proofs.Erdos85OneHighInternalEdgeSameMiss
import Proofs.Erdos85OneHighRepeatedPairTargets

/-! # Structural obstruction from a repeated exchanged miss pair -/

namespace Erdos85

noncomputable section

/-- Equality of canonical min/max representatives decodes to equality of
ordered endpoints up to reversal. -/
theorem eq_or_swap_of_minMax_pair_eq
    {L : Type*} [LinearOrder L]
    {a b c d : L} (hab : a ≠ b) (hcd : c ≠ d)
    (hpair : (min a b, max a b) = (min c d, max c d)) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rcases lt_or_gt_of_ne hab with hablt | hbalt <;>
    rcases lt_or_gt_of_ne hcd with hcdlt | hdclt
  · rw [min_eq_left hablt.le, max_eq_right hablt.le,
      min_eq_left hcdlt.le, max_eq_right hcdlt.le] at hpair
    exact Or.inl (Prod.mk.inj hpair)
  · rw [min_eq_left hablt.le, max_eq_right hablt.le,
      min_eq_right hdclt.le, max_eq_left hdclt.le] at hpair
    exact Or.inr (Prod.mk.inj hpair)
  · rw [min_eq_right hbalt.le, max_eq_left hbalt.le,
      min_eq_left hcdlt.le, max_eq_right hcdlt.le] at hpair
    have h := Prod.mk.inj hpair
    exact Or.inr ⟨h.2, h.1⟩
  · rw [min_eq_right hbalt.le, max_eq_left hbalt.le,
      min_eq_right hdclt.le, max_eq_left hdclt.le] at hpair
    have h := Prod.mk.inj hpair
    exact Or.inl ⟨h.2, h.1⟩

/-- Canonical two-edge graph specialization: parity and nonconstancy leave
exactly the same-or-reversed repeated miss-label assignment. -/
theorem canonicalTwoEdge_missingLabels_same_or_reversed_of_even
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (s : {z : V // z ∈ G.neighborSet v})
    (e : secondLayerBranch G v s ≃ Fin 5)
    (hcanonical : ∀ x y, decide (G.Adj x.1 y.1) =
      oneHighCanonicalBranchAdj true (e x) (e y))
    (heven : ∀ u ∈ ((Finset.univ.erase s).erase (rootMate s)),
      Even (highBranchMissCount G v s u))
    (h01 : oneHighMissingBranch G v rootMate s ((e.symm 0).1) ≠
      oneHighMissingBranch G v rootMate s ((e.symm 1).1))
    (h23 : oneHighMissingBranch G v rootMate s ((e.symm 2).1) ≠
      oneHighMissingBranch G v rootMate s ((e.symm 3).1)) :
    (oneHighMissingBranch G v rootMate s ((e.symm 0).1) =
        oneHighMissingBranch G v rootMate s ((e.symm 2).1) ∧
      oneHighMissingBranch G v rootMate s ((e.symm 1).1) =
        oneHighMissingBranch G v rootMate s ((e.symm 3).1)) ∨
    (oneHighMissingBranch G v rootMate s ((e.symm 0).1) =
        oneHighMissingBranch G v rootMate s ((e.symm 3).1) ∧
      oneHighMissingBranch G v rootMate s ((e.symm 1).1) =
        oneHighMissingBranch G v rootMate s ((e.symm 2).1)) := by
  apply eq_or_swap_of_minMax_pair_eq h01 h23
  exact canonicalTwoEdge_missingPair_eq_of_even G hfree hv hexternal
    houterDegree rootMate hrootAdj s e hcanonical heven h01 h23

structure OneHighRepeatedPairSeparatedConfiguration
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V)
    (s : {z : V // z ∈ G.neighborSet v}) where
  u : {z : V // z ∈ G.neighborSet v}
  w : {z : V // z ∈ G.neighborSet v}
  source_ne_u : s ≠ u
  source_ne_w : s ≠ w
  u_ne_w : u ≠ w
  x₁ : V
  y₁ : V
  x₂ : V
  y₂ : V
  x₁_mem : x₁ ∈ secondLayerBranch G v s
  y₁_mem : y₁ ∈ secondLayerBranch G v s
  x₂_mem : x₂ ∈ secondLayerBranch G v s
  y₂_mem : y₂ ∈ secondLayerBranch G v s
  edge₁ : G.Adj x₁ y₁
  edge₂ : G.Adj x₂ y₂
  q₁ : OneHighExchangedCrossWitness G v u w x₁ y₁
  q₂ : OneHighExchangedCrossWitness G v u w x₂ y₂
  uTargets_ne : q₁.uTarget ≠ q₂.uTarget
  wTargets_ne : q₁.wTarget ≠ q₂.wTarget

/-- Full canonical instantiation of the repeated-pair obstruction. -/
theorem exists_repeatedPairSeparatedConfiguration_of_canonicalTwoEdge_even
    {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (s : {z : V // z ∈ G.neighborSet v})
    (e : secondLayerBranch G v s ≃ Fin 5)
    (hcanonical : ∀ x y, decide (G.Adj x.1 y.1) =
      oneHighCanonicalBranchAdj true (e x) (e y))
    (heven : ∀ u ∈ ((Finset.univ.erase s).erase (rootMate s)),
      Even (highBranchMissCount G v s u))
    (h01 : oneHighMissingBranch G v rootMate s ((e.symm 0).1) ≠
      oneHighMissingBranch G v rootMate s ((e.symm 1).1))
    (h23 : oneHighMissingBranch G v rootMate s ((e.symm 2).1) ≠
      oneHighMissingBranch G v rootMate s ((e.symm 3).1)) :
    Nonempty (OneHighRepeatedPairSeparatedConfiguration G v s) := by
  let label : Fin 5 → {z : V // z ∈ G.neighborSet v} := fun r =>
    oneHighMissingBranch G v rootMate s ((e.symm r).1)
  have hmatched (r : Fin 5) (hr : r.val < 4) :
      (G.neighborFinset ((e.symm r).1) ∩
        secondLayerBranch G v s).card = 1 :=
    card_neighbor_inter_branch_eq_one_of_canonicalTrue_lt_four
      G hfree v s e hcanonical r hr
  have hlabelMem (r : Fin 5) (hr : r.val < 4) :
      label r ∈ ((Finset.univ.erase s).erase (rootMate s)) := by
    have hm := oneHighMissingBranch_mem_of_matched G hfree hv hexternal
      houterDegree rootMate hrootAdj s ((e.symm r).1) (e.symm r).2
      (hmatched r hr)
    exact (Finset.mem_filter.mp hm).1
  have hsees (r : Fin 5) (hr : r.val < 4)
      (z : {q : V // q ∈ G.neighborSet v})
      (hz : z ∈ ((Finset.univ.erase s).erase (rootMate s)))
      (hne : z ≠ label r) :
      (G.neighborFinset ((e.symm r).1) ∩
        secondLayerBranch G v z).card ≠ 0 := by
    intro hzero
    have hzMiss : z ∈ oneHighFarMissBranches G v rootMate s
        ((e.symm r).1) := Finset.mem_filter.mpr ⟨hz, hzero⟩
    have heq := eq_oneHighMissingBranch_of_matched_of_mem G hfree hv
      hexternal houterDegree rootMate hrootAdj s ((e.symm r).1)
      (e.symm r).2 (hmatched r hr) z hzMiss
    exact hne heq
  have hadj (r t : Fin 5)
      (hc : oneHighCanonicalBranchAdj true r t = true) :
      G.Adj (e.symm r).1 (e.symm t).1 := by
    apply of_decide_eq_true
    rw [hcanonical, e.apply_symm_apply, e.apply_symm_apply]
    exact hc
  have hadj01 : G.Adj (e.symm 0).1 (e.symm 1).1 :=
    hadj 0 1 (by decide)
  have hadj23 : G.Adj (e.symm 2).1 (e.symm 3).1 :=
    hadj 2 3 (by decide)
  have hcoordNe {r t : Fin 5} (hrt : r ≠ t) :
      (e.symm r).1 ≠ (e.symm t).1 := by
    intro h
    apply hrt
    exact e.symm.injective (Subtype.ext h)
  have horient := canonicalTwoEdge_missingLabels_same_or_reversed_of_even
    G hfree hv hexternal houterDegree rootMate hrootAdj s e hcanonical
      heven h01 h23
  let u := label 0
  let w := label 1
  have huMem : u ∈ ((Finset.univ.erase s).erase (rootMate s)) :=
    hlabelMem 0 (by decide)
  have hwMem : w ∈ ((Finset.univ.erase s).erase (rootMate s)) :=
    hlabelMem 1 (by decide)
  have hsu : s ≠ u := by
    exact Ne.symm (Finset.mem_erase.mp (Finset.mem_erase.mp huMem).2).1
  have hsw : s ≠ w := by
    exact Ne.symm (Finset.mem_erase.mp (Finset.mem_erase.mp hwMem).2).1
  have huw : u ≠ w := by simpa [u, w, label] using h01
  rcases horient with hsame | hrev
  · obtain ⟨q₁, q₂, hqu, hqw⟩ :=
      exists_separated_crossTargets_of_two_internalEdges G hfree hsu hsw
        (e.symm 0).2 (e.symm 1).2 (e.symm 2).2 (e.symm 3).2
        hadj01 hadj23 (hcoordNe (by decide)) (hcoordNe (by decide))
        (hsees 1 (by decide) u huMem (by simpa [u, label] using h01))
        (hsees 0 (by decide) w hwMem (by simpa [w, label] using h01.symm))
        (hsees 3 (by decide) u huMem (by
          intro h
          apply h01
          change label 0 = label 1
          calc label 0 = u := rfl
            _ = label 3 := h
            _ = label 1 := hsame.2.symm))
        (hsees 2 (by decide) w hwMem (by
          intro h
          apply h01
          change label 0 = label 1
          calc label 0 = label 2 := hsame.1
            _ = w := h.symm
            _ = label 1 := rfl))
    exact ⟨⟨u, w, hsu, hsw, huw, (e.symm 0).1, (e.symm 1).1,
      (e.symm 2).1, (e.symm 3).1, (e.symm 0).2, (e.symm 1).2,
      (e.symm 2).2, (e.symm 3).2, hadj01, hadj23, q₁, q₂, hqu, hqw⟩⟩
  · obtain ⟨q₁, q₂, hqu, hqw⟩ :=
      exists_separated_crossTargets_of_two_internalEdges G hfree hsu hsw
        (e.symm 0).2 (e.symm 1).2 (e.symm 3).2 (e.symm 2).2
        hadj01 hadj23.symm (hcoordNe (by decide)) (hcoordNe (by decide))
        (hsees 1 (by decide) u huMem (by simpa [u, label] using h01))
        (hsees 0 (by decide) w hwMem (by simpa [w, label] using h01.symm))
        (hsees 2 (by decide) u huMem (by
          intro h
          apply h01
          change label 0 = label 1
          calc label 0 = u := rfl
            _ = label 2 := h
            _ = label 1 := hrev.2.symm))
        (hsees 3 (by decide) w hwMem (by
          intro h
          apply h01
          change label 0 = label 1
          calc label 0 = label 3 := hrev.1
            _ = w := h.symm
            _ = label 1 := rfl))
    exact ⟨⟨u, w, hsu, hsw, huw, (e.symm 0).1, (e.symm 1).1,
      (e.symm 3).1, (e.symm 2).1, (e.symm 0).2, (e.symm 1).2,
      (e.symm 3).2, (e.symm 2).2, hadj01, hadj23.symm, q₁, q₂, hqu, hqw⟩⟩

end

end Erdos85
