import Proofs.Erdos85NegativeSignedJointConnectedMatrixDecomposition

/-! # The alternating eigenline of the C16 distance-two graph -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

set_option maxRecDepth 100000 in
/-- Every vertex of the fixed `C16` distance-two graph has degree two. -/
theorem sixteenCycleOffsetTwo_card :
    ∀ i : Fin 16,
      ((Finset.univ : Finset (Fin 16)).filter
        fun j ↦ sixteenCycleOffsetTwo i j).card = 2 := by
  native_decide

/-- Any signing which flips across the edges of a labeled `C16` is a
`2`-eigenvector of its fixed distance-two graph: two flips preserve sign,
and there are exactly two vertices at distance two. -/
theorem connectedC16DistanceTwoMatrix_mulVec_of_flip
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (label : SixteenCycleLabeling H)
    (s : V → ℤ)
    (hflip : ∀ {x y}, H.Adj x y → s x = -s y) :
    connectedC16DistanceTwoMatrix.mulVec
        (fun i ↦ s (label.toEquiv.symm i)) =
      fun i ↦ 2 * s (label.toEquiv.symm i) := by
  funext i
  let S := (Finset.univ : Finset (Fin 16)).filter
    fun j ↦ sixteenCycleOffsetTwo i j
  have hsame : ∀ j ∈ S,
      s (label.toEquiv.symm j) = s (label.toEquiv.symm i) := by
    intro j hj
    have hoff := (Finset.mem_filter.mp hj).2
    have hij : i ≠ j := by
      intro h
      subst j
      simp [sixteenCycleOffsetTwo] at hoff
    obtain ⟨z, hiz, hjz⟩ :=
      (sixteenCycleLabeling_internalCommon_iff_offsetTwo
        H label i j hij).mpr hoff
    rw [hflip hiz, hflip hjz]
  change ∑ j, connectedC16DistanceTwoMatrix i j *
      s (label.toEquiv.symm j) = _
  have hsum : ∑ j ∈ S, s (label.toEquiv.symm j) =
      2 * s (label.toEquiv.symm i) := by
    calc
      _ = ∑ _j ∈ S, s (label.toEquiv.symm i) :=
        Finset.sum_congr rfl hsame
      _ = (S.card : ℤ) * s (label.toEquiv.symm i) := by simp
      _ = 2 * s (label.toEquiv.symm i) := by
        rw [sixteenCycleOffsetTwo_card i]
        norm_num
  rw [← hsum]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : sixteenCycleOffsetTwo i j <;>
    simp [connectedC16DistanceTwoMatrix, h]

end

end Erdos85

#print axioms Erdos85.sixteenCycleOffsetTwo_card
#print axioms Erdos85.connectedC16DistanceTwoMatrix_mulVec_of_flip
