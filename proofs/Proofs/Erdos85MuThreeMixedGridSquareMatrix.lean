import Proofs.Erdos85MuThreeMixedGridSquareDegrees
import Proofs.Erdos85ConflictMatrixPolynomial

/-!
# Matrix form of the mixed-grid square partition

The exact entrywise identity is

`A_C² + A_D + A_Rowcol = 5 I + J`.

This packages both uses of C4-freeness: the exterior square is a zero-one
matrix off the diagonal, and the missing entries split into the residual
defect and rook relations.
-/

open SimpleGraph

namespace Erdos85

/-- **Mixed-grid square matrix identity.** -/
theorem MuThreeMixedGridCode.adjMatrix_sq_add_residual_add_rowColumn
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    C.adjMatrix ℤ * C.adjMatrix ℤ +
          (mixedGridSquareResidualGraph K C).adjMatrix ℤ +
          (mixedGridRowColumnGraph K).adjMatrix ℤ =
      (5 : ℤ) • (1 : Matrix (muThreeMixedCell K) (muThreeMixedCell K) ℤ) +
        FriendshipTheoremOQ01.onesMatrix (muThreeMixedCell K) := by
  ext u v
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    FriendshipTheoremOQ01.onesMatrix, Matrix.of_apply, smul_eq_mul]
  by_cases huv : u = v
  · subst v
    rw [C.adjMatrix_mul_self_apply_self,
      MuThreeMixedGridCode.degree_eq_six H K C code u]
    simp [SimpleGraph.adjMatrix_apply]
  · rw [adjMatrix_sq_apply_eq_card_common]
    let n := (C.neighborFinset u ∩ C.neighborFinset v).card
    have hnle : n ≤ 1 :=
      MuThreeMixedGridCode.common_neighbor_card_le_one H K C code u v huv
    by_cases hrook : (mixedGridRowColumnGraph K).Adj u v
    · have hnzero : n = 0 :=
        MuThreeMixedGridCode.rowColumn_common_neighbor_card_eq_zero
          H K C code hrook
      have hd : ¬ (mixedGridSquareResidualGraph K C).Adj u v := by
        intro h
        exact h.2.1 hrook
      simp [SimpleGraph.adjMatrix_apply, huv, hrook, hd, n, hnzero]
    · by_cases hnzero : n = 0
      · have hd : (mixedGridSquareResidualGraph K C).Adj u v :=
          ⟨huv, hrook, hnzero⟩
        simp [SimpleGraph.adjMatrix_apply, huv, hrook, hd, n, hnzero]
      · have hnone : n = 1 := by omega
        have hd : ¬ (mixedGridSquareResidualGraph K C).Adj u v := by
          intro h
          apply hnzero
          exact h.2.2
        simp [SimpleGraph.adjMatrix_apply, huv, hrook, hd, n, hnone]

end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.adjMatrix_sq_add_residual_add_rowColumn
