import Proofs.Erdos85MuThreeMixedGridZeroSector

/-!
# The square operator on the zero row/column sector

On the invariant residual sector the all-ones term vanishes, so the mixed
square identity becomes `A_D + A_R = 5I - A_C²`.
-/

open SimpleGraph

namespace Erdos85

/-- The all-ones matrix annihilates the zero row/column sector. -/
theorem MixedGridZeroRowColumn.onesMatrix_mulVec_eq_zero
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {K : X → Y → Prop} [DecidableRel K]
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f) :
    (FriendshipTheoremOQ01.onesMatrix (muThreeMixedCell K)).mulVec f = 0 := by
  funext u
  simp [FriendshipTheoremOQ01.onesMatrix, Matrix.mulVec, dotProduct,
    hf.sum_eq_zero]

/-- The zero row/column predicate is closed under integer scaling. -/
theorem MixedGridZeroRowColumn.smul
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {K : X → Y → Prop} [DecidableRel K]
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f) (a : ℤ) :
    MixedGridZeroRowColumn K (a • f) := by
  constructor
  · intro x
    rw [dotProduct]
    calc
      ∑ i, mixedGridRowIndicator K x i * (a • f) i =
          a * ∑ i, mixedGridRowIndicator K x i * f i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      _ = 0 := by rw [← dotProduct, hf.1 x]; simp
  · intro y
    rw [dotProduct]
    calc
      ∑ i, mixedGridColumnIndicator K y i * (a • f) i =
          a * ∑ i, mixedGridColumnIndicator K y i * f i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      _ = 0 := by rw [← dotProduct, hf.2 y]; simp

/-- The zero row/column predicate is closed under subtraction. -/
theorem MixedGridZeroRowColumn.sub
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {K : X → Y → Prop} [DecidableRel K]
    {f g : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f)
    (hg : MixedGridZeroRowColumn K g) :
    MixedGridZeroRowColumn K (f - g) := by
  constructor
  · intro x
    rw [dotProduct]
    calc
      ∑ i, mixedGridRowIndicator K x i * (f - g) i =
          (∑ i, mixedGridRowIndicator K x i * f i) -
            ∑ i, mixedGridRowIndicator K x i * g i := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Pi.sub_apply]
        ring
      _ = 0 := by rw [← dotProduct, hf.1 x, ← dotProduct, hg.1 x]; simp
  · intro y
    rw [dotProduct]
    calc
      ∑ i, mixedGridColumnIndicator K y i * (f - g) i =
          (∑ i, mixedGridColumnIndicator K y i * f i) -
            ∑ i, mixedGridColumnIndicator K y i * g i := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Pi.sub_apply]
        ring
      _ = 0 := by rw [← dotProduct, hf.2 y, ← dotProduct, hg.2 y]; simp

/-- **Restricted square identity.** On the zero row/column sector, the
combined residual-plus-rook action is `5I - A_C²`. -/
theorem MuThreeMixedGridCode.residual_add_rowColumn_mulVec_eq_on_zeroSector
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f) :
    ((mixedGridSquareResidualGraph K C).adjMatrix ℤ +
        (mixedGridRowColumnGraph K).adjMatrix ℤ).mulVec f =
      (5 : ℤ) • f -
        (C.adjMatrix ℤ).mulVec ((C.adjMatrix ℤ).mulVec f) := by
  have hmat :=
    MuThreeMixedGridCode.residual_add_rowColumn_adjMatrix_eq H K C code
  have h := congrArg (fun M => M.mulVec f) hmat
  simp only [Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec] at h
  rw [hf.onesMatrix_mulVec_eq_zero, add_zero] at h
  rw [← Matrix.mulVec_mulVec] at h
  rw [Matrix.add_mulVec]
  exact h

/-- The combined residual-plus-rook operator preserves the residual sector. -/
theorem MuThreeMixedGridCode.zeroRowColumn_residual_add_rowColumn_invariant
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f) :
    MixedGridZeroRowColumn K
      (((mixedGridSquareResidualGraph K C).adjMatrix ℤ +
        (mixedGridRowColumnGraph K).adjMatrix ℤ).mulVec f) := by
  rw [MuThreeMixedGridCode.residual_add_rowColumn_mulVec_eq_on_zeroSector
    H K C code hf]
  have hf1 := MuThreeMixedGridCode.zeroRowColumn_adjMatrix_invariant
    H K C code hf
  have hf2 := MuThreeMixedGridCode.zeroRowColumn_adjMatrix_invariant
    H K C code hf1
  exact MixedGridZeroRowColumn.sub (MixedGridZeroRowColumn.smul hf 5)
    hf2

end Erdos85

#print axioms Erdos85.MixedGridZeroRowColumn.onesMatrix_mulVec_eq_zero
#print axioms
  Erdos85.MuThreeMixedGridCode.residual_add_rowColumn_mulVec_eq_on_zeroSector
#print axioms
  Erdos85.MuThreeMixedGridCode.zeroRowColumn_residual_add_rowColumn_invariant
