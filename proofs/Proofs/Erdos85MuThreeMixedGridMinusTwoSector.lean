import Proofs.Erdos85MuThreeMixedGridCommutators

/-!
# The rook `-2` sector of a mixed `mu = 3` grid

On a zero-sum vector in the `-2` eigenspace of the occupied rook graph, the
square partition collapses to

`D f = 7 f - C² f`.

The commutator package shows that this sector is invariant under both `C`
and `D`; the theorem below records the exact integral action needed by later
spectral and Galois arguments.
-/

namespace Erdos85

/-- A zero-sum integral vector is killed by the all-ones matrix. -/
theorem onesMatrix_mulVec_eq_zero_of_sum_eq_zero
    {V : Type*} [Fintype V]
    (f : V → ℤ) (hsum : ∑ v, f v = 0) :
    (FriendshipTheoremOQ01.onesMatrix V).mulVec f = 0 := by
  funext v
  simp [FriendshipTheoremOQ01.onesMatrix, Matrix.mulVec, dotProduct, hsum]

/-- **Exact `-2`-sector action.**  If `f` is zero-sum and the rook graph acts
by `-2`, then the residual graph acts by `7 - C²`. -/
theorem MuThreeMixedGridCode.squareResidual_mulVec_of_rowColumn_negTwo
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (f : muThreeMixedCell K → ℤ)
    (hsum : ∑ u, f u = 0)
    (hnegTwo : (mixedGridRowColumnGraph K).adjMatrix ℤ |>.mulVec f =
      (-2 : ℤ) • f) :
    (mixedGridSquareResidualGraph K C).adjMatrix ℤ |>.mulVec f =
      (7 : ℤ) • f - C.adjMatrix ℤ |>.mulVec
        (C.adjMatrix ℤ |>.mulVec f) := by
  have hsq := code.adjMatrix_sq_add_residual_add_rowColumn H K C
  have haction := congrArg (fun M : Matrix (muThreeMixedCell K)
      (muThreeMixedCell K) ℤ => M.mulVec f) hsq
  have hJ := onesMatrix_mulVec_eq_zero_of_sum_eq_zero f hsum
  simp only [Matrix.add_mulVec, Matrix.mul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec] at haction
  rw [hnegTwo, hJ] at haction
  funext u
  have hu := congrFun haction u
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, Pi.zero_apply,
    smul_eq_mul] at hu ⊢
  omega

/-- Commutation makes the rook `-2` eigenspace invariant under exterior
adjacency. -/
theorem MuThreeMixedGridCode.adjMatrix_mulVec_preserves_rowColumn_negTwo
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (f : muThreeMixedCell K → ℤ)
    (hnegTwo : (mixedGridRowColumnGraph K).adjMatrix ℤ |>.mulVec f =
      (-2 : ℤ) • f) :
    (mixedGridRowColumnGraph K).adjMatrix ℤ |>.mulVec
        (C.adjMatrix ℤ |>.mulVec f) =
      (-2 : ℤ) • (C.adjMatrix ℤ |>.mulVec f) := by
  rw [← Matrix.mul_mulVec,
    code.adjMatrix_commutes_rowColumn H K C |>.symm,
    Matrix.mul_mulVec, hnegTwo]
  simp

/-- The same `-2` eigenspace is invariant under the residual relation. -/
theorem MuThreeMixedGridCode.squareResidual_mulVec_preserves_rowColumn_negTwo
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (f : muThreeMixedCell K → ℤ)
    (hnegTwo : (mixedGridRowColumnGraph K).adjMatrix ℤ |>.mulVec f =
      (-2 : ℤ) • f) :
    (mixedGridRowColumnGraph K).adjMatrix ℤ |>.mulVec
        ((mixedGridSquareResidualGraph K C).adjMatrix ℤ |>.mulVec f) =
      (-2 : ℤ) •
        ((mixedGridSquareResidualGraph K C).adjMatrix ℤ |>.mulVec f) := by
  rw [← Matrix.mul_mulVec,
    code.rowColumn_commutes_squareResidual H K C,
    Matrix.mul_mulVec, hnegTwo]
  simp

end Erdos85

#print axioms Erdos85.onesMatrix_mulVec_eq_zero_of_sum_eq_zero
#print axioms
  Erdos85.MuThreeMixedGridCode.squareResidual_mulVec_of_rowColumn_negTwo
#print axioms
  Erdos85.MuThreeMixedGridCode.adjMatrix_mulVec_preserves_rowColumn_negTwo
#print axioms
  Erdos85.MuThreeMixedGridCode.squareResidual_mulVec_preserves_rowColumn_negTwo
