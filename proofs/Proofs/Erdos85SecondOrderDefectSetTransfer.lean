import Proofs.Erdos85NonregularDefectOperator

/-!
# Set transfer through the nonregular second-order defect identity

Applying `A² = diag(degree - 1) + J - D` to the characteristic vector of a
finite vertex set turns a two-level original-neighbor partition into exact
defect-neighbor counts.  This is the reusable pointwise form needed by the
order-nine articulation equality eliminations.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The integral characteristic vector of a vertex finset. -/
def finsetIndicatorInt {V : Type*} [DecidableEq V] (R : Finset V) : V → ℤ :=
  fun x ↦ if x ∈ R then 1 else 0

@[simp] theorem finsetIndicatorInt_apply {V : Type*} [DecidableEq V]
    (R : Finset V) (x : V) :
    finsetIndicatorInt R x = if x ∈ R then 1 else 0 := rfl

/-- Adjacency applied to a characteristic vector counts neighbors in the set. -/
theorem adjMatrix_mulVec_finsetIndicatorInt_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (R : Finset V) (x : V) :
    (G.adjMatrix ℤ).mulVec (finsetIndicatorInt R) x =
      ((G.neighborFinset x ∩ R).card : ℤ) := by
  classical
  rw [G.adjMatrix_mulVec_apply]
  simp [finsetIndicatorInt]

/-- The all-ones matrix applied to a characteristic vector records its size. -/
theorem onesMatrix_mulVec_finsetIndicatorInt_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : Finset V) (x : V) :
    (FriendshipTheoremOQ01.onesMatrix V).mulVec
        (finsetIndicatorInt R) x = (R.card : ℤ) := by
  classical
  simp [Matrix.mulVec, dotProduct, finsetIndicatorInt,
    FriendshipTheoremOQ01.onesMatrix]

/-- **Pointwise nonregular set-transfer identity.**  The number of defect
neighbors of `x` in `R` is the diagonal contribution at `x`, plus `|R|`,
minus the sum over original neighbors of their incidences with `R`.

All terms are stated over `ℤ`, so the degree-predecessor term is exact even
at isolated vertices and no truncated subtraction enters the identity. -/
theorem c4Free_secondOrderDefect_neighbor_inter_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (R : Finset V) (x : V) :
    (((secondOrderDefectGraph G).neighborFinset x ∩ R).card : ℤ) =
      ((G.degree x : ℤ) - 1) * (if x ∈ R then 1 else 0) + (R.card : ℤ) -
        ∑ y ∈ G.neighborFinset x,
          ((G.neighborFinset y ∩ R).card : ℤ) := by
  classical
  let A := G.adjMatrix ℤ
  let D := (secondOrderDefectGraph G).adjMatrix ℤ
  let f := finsetIndicatorInt R
  have hmatrix :=
    adjMatrix_sq_eq_degreePredDiagonal_add_ones_sub_secondOrderDefect G hfree
  have hv := congrArg (fun M : Matrix V V ℤ ↦ M.mulVec f) hmatrix
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec] at hv
  have hx := congrFun hv x
  dsimp only [f] at hx
  rw [G.adjMatrix_mulVec_apply] at hx
  simp_rw [adjMatrix_mulVec_finsetIndicatorInt_apply] at hx
  simp only [Pi.add_apply, Pi.sub_apply] at hx
  rw [
    onesMatrix_mulVec_finsetIndicatorInt_apply,
    adjMatrix_mulVec_finsetIndicatorInt_apply] at hx
  have hdiag : (degreePredDiagonal G).mulVec (finsetIndicatorInt R) x =
      ((G.degree x : ℤ) - 1) * (if x ∈ R then 1 else 0) := by
    by_cases hxR : x ∈ R <;>
      simp [degreePredDiagonal, Matrix.mulVec, dotProduct,
        Matrix.diagonal_apply, finsetIndicatorInt, hxR]
  rw [hdiag] at hx
  omega

end

end Erdos85

#print axioms Erdos85.c4Free_secondOrderDefect_neighbor_inter_card_eq
