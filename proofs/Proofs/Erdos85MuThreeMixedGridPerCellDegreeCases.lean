import Proofs.Erdos85MuThreeMixedGridPerCellCommonMates
import Proofs.Erdos85MuThreeMixedGridPerCellColumnMates

/-! # Degree cases of the exact per-cell residual row law -/

open SimpleGraph

namespace Erdos85

/-- Residual degree two toward a target row occurs exactly when the two
source/target rows have no common `H`-column and the rook coordinate in the
target row is a forbidden `K`-cell. -/
theorem MuThreeMixedGridCode.residualMatesInRow_card_eq_two_iff
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : X) (hxu : x ≠ u.1.1) :
    (mixedGridGraphMatesInRow
        (mixedGridSquareResidualGraph K C) u x).card = 2 ↔
      (mixedGridHCommonColumns H u.1.1 x).card = 0 ∧ K x u.1.2 := by
  have h := code.residualMatesInRow_add_overlap_add_indicator
    H K C u x hxu
  by_cases hK : K x u.1.2
  · rw [if_pos hK] at h
    constructor
    · intro htwo
      exact ⟨by omega, hK⟩
    · rintro ⟨hzero, _⟩
      omega
  · rw [if_neg hK] at h
    constructor
    · intro htwo
      omega
    · rintro ⟨_, hbad⟩
      exact (hK hbad).elim

/-- The degree-one branch splits into its two possible overlap/rook cases. -/
theorem MuThreeMixedGridCode.residualMatesInRow_card_eq_one_iff
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : X) (hxu : x ≠ u.1.1) :
    (mixedGridGraphMatesInRow
        (mixedGridSquareResidualGraph K C) u x).card = 1 ↔
      ((mixedGridHCommonColumns H u.1.1 x).card = 1 ∧ K x u.1.2) ∨
      ((mixedGridHCommonColumns H u.1.1 x).card = 0 ∧ ¬ K x u.1.2) := by
  have h := code.residualMatesInRow_add_overlap_add_indicator
    H K C u x hxu
  by_cases hK : K x u.1.2
  · rw [if_pos hK] at h
    constructor
    · intro hone
      exact Or.inl ⟨by omega, hK⟩
    · rintro (⟨hoverlap, _⟩ | ⟨_, hnK⟩)
      · omega
      · exact (hnK hK).elim
  · rw [if_neg hK] at h
    constructor
    · intro hone
      exact Or.inr ⟨by omega, hK⟩
    · rintro (⟨_, hbad⟩ | ⟨hoverlap, _⟩)
      · exact (hK hbad).elim
      · omega

/-- The degree-zero branch is the complementary pair of cases. -/
theorem MuThreeMixedGridCode.residualMatesInRow_card_eq_zero_iff
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : X) (hxu : x ≠ u.1.1) :
    (mixedGridGraphMatesInRow
        (mixedGridSquareResidualGraph K C) u x).card = 0 ↔
      ((mixedGridHCommonColumns H u.1.1 x).card = 2 ∧ K x u.1.2) ∨
      ((mixedGridHCommonColumns H u.1.1 x).card = 1 ∧ ¬ K x u.1.2) := by
  have h := code.residualMatesInRow_add_overlap_add_indicator
    H K C u x hxu
  by_cases hK : K x u.1.2
  · rw [if_pos hK] at h
    constructor
    · intro hzero
      exact Or.inl ⟨by omega, hK⟩
    · rintro (⟨hoverlap, _⟩ | ⟨_, hnK⟩)
      · omega
      · exact (hnK hK).elim
  · rw [if_neg hK] at h
    constructor
    · intro hzero
      exact Or.inr ⟨by omega, hK⟩
    · rintro (⟨_, hbad⟩ | ⟨hoverlap, _⟩)
      · exact (hK hbad).elim
      · omega

/-- Column-dual degree-two trigger. -/
theorem MuThreeMixedGridCode.residualMatesInColumn_card_eq_two_iff
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (y : Y) (hyu : y ≠ u.1.2) :
    (mixedGridGraphMatesInColumn
        (mixedGridSquareResidualGraph K C) u y).card = 2 ↔
      (mixedGridHCommonRows H u.1.2 y).card = 0 ∧ K u.1.1 y := by
  have h := code.residualMatesInColumn_add_overlap_add_indicator
    H K C u y hyu
  by_cases hK : K u.1.1 y
  · rw [if_pos hK] at h
    constructor
    · intro htwo
      exact ⟨by omega, hK⟩
    · rintro ⟨hzero, _⟩
      omega
  · rw [if_neg hK] at h
    constructor
    · intro htwo
      omega
    · rintro ⟨_, hbad⟩
      exact (hK hbad).elim

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.residualMatesInRow_card_eq_two_iff
#print axioms Erdos85.MuThreeMixedGridCode.residualMatesInRow_card_eq_one_iff
#print axioms Erdos85.MuThreeMixedGridCode.residualMatesInRow_card_eq_zero_iff
#print axioms Erdos85.MuThreeMixedGridCode.residualMatesInColumn_card_eq_two_iff
