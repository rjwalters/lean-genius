import Proofs.Erdos85MuThreeMixedGridIndicatorAction

/-!
# The invariant zero-row/zero-column sector

The orthogonal complement of the row/column indicator span consists of
vectors whose sum on every occupied row and every occupied column is zero.
The forced indicator formulas imply that the exterior adjacency operator
preserves this sector.
-/

open SimpleGraph

namespace Erdos85

/-- Simultaneously zero sum on every occupied row and column. -/
def MixedGridZeroRowColumn
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K]
    (f : muThreeMixedCell K → ℤ) : Prop :=
  (∀ x, mixedGridRowIndicator K x ⬝ᵥ f = 0) ∧
  (∀ y, mixedGridColumnIndicator K y ⬝ᵥ f = 0)

/-- Zero row sums already force zero total sum. -/
theorem MixedGridZeroRowColumn.sum_eq_zero
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {K : X → Y → Prop} [DecidableRel K]
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f) : ∑ u, f u = 0 := by
  calc
    ∑ u, f u = ∑ x : X, mixedGridRowIndicator K x ⬝ᵥ f := by
      simp [dotProduct, mixedGridRowIndicator, Finset.sum_comm]
    _ = 0 := by simp [hf.1]

/-- Symmetry transports dot products across the exterior adjacency matrix. -/
theorem mixedGridIndicator_dot_adjMatrix_mulVec
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {K : X → Y → Prop} [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (a f : muThreeMixedCell K → ℤ) :
    a ⬝ᵥ (C.adjMatrix ℤ).mulVec f =
      (C.adjMatrix ℤ).mulVec a ⬝ᵥ f := by
  rw [Matrix.dotProduct_mulVec]
  have hsymm : (C.adjMatrix ℤ).transpose = C.adjMatrix ℤ :=
    C.isSymm_adjMatrix.eq
  rw [← hsymm, Matrix.vecMul_transpose, hsymm]

/-- **Invariant residual sector.** The exterior adjacency operator preserves
simultaneous zero row and column sums. -/
theorem MuThreeMixedGridCode.zeroRowColumn_adjMatrix_invariant
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {f : muThreeMixedCell K → ℤ}
    (hf : MixedGridZeroRowColumn K f) :
    MixedGridZeroRowColumn K ((C.adjMatrix ℤ).mulVec f) := by
  have htotal := hf.sum_eq_zero
  constructor
  · intro x
    rw [mixedGridIndicator_dot_adjMatrix_mulVec C,
      MuThreeMixedGridCode.adjMatrix_mulVec_rowIndicator_eq H K C code x]
    simp only [dotProduct, Pi.sub_apply, Finset.sum_apply, sub_mul,
      Finset.sum_mul]
    rw [Finset.sum_sub_distrib]
    simp only [one_mul, htotal, zero_sub, neg_eq_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    change mixedGridColumnIndicator K i ⬝ᵥ f = 0
    exact hf.2 i
  · intro y
    rw [mixedGridIndicator_dot_adjMatrix_mulVec C,
      MuThreeMixedGridCode.adjMatrix_mulVec_columnIndicator_eq H K C code y]
    simp only [dotProduct, Pi.sub_apply, Finset.sum_apply, sub_mul,
      Finset.sum_mul]
    rw [Finset.sum_sub_distrib]
    simp only [one_mul, htotal, zero_sub, neg_eq_zero]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i hi
    change mixedGridRowIndicator K i ⬝ᵥ f = 0
    exact hf.1 i

end Erdos85

#print axioms Erdos85.MixedGridZeroRowColumn.sum_eq_zero
#print axioms Erdos85.MuThreeMixedGridCode.zeroRowColumn_adjMatrix_invariant
