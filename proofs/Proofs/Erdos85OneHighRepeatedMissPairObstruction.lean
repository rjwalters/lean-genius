import Proofs.Erdos85OneHighTwoEdgeMissMultiplicity
import Proofs.Erdos85OneHighInternalEdgeSameMiss

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

end

end Erdos85
