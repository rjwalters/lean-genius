import Proofs.Erdos85CrossNeighborhoodFlipMatrix

/-!
# Defect expansion of the cross-neighborhood flip commutator

Substituting the square identity `A² = D + J + I` into `(73rnz_cjibky)`
isolates two weighted star sums and the genuine defect commutator.  This is
the exact algebraic content of `(73rnz_cjibkza)`.
-/

open SimpleGraph

namespace Erdos85

/-- At nonadjacent roots, the identity terms in the square expansion vanish.
The two all-ones terms are precisely the endpoint-weighted star sums. -/
theorem crossNeighborhood_flipMatrix_eq_starSums_add_defectCommutator
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : SimpleGraph V) [DecidableRel A.Adj]
    (D J : Matrix V V (ZMod 2)) (b : V → ZMod 2)
    (hJ : ∀ i j, J i j = 1)
    (hSquare : A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2) =
      D + J + 1)
    {E G : V} (hEG : ¬ A.Adj E G) :
    (A.adjMatrix (ZMod 2) * Matrix.diagonal b *
          (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2)) +
        (A.adjMatrix (ZMod 2) * A.adjMatrix (ZMod 2)) *
          Matrix.diagonal b * A.adjMatrix (ZMod 2)) E G =
      (∑ x, A.adjMatrix (ZMod 2) E x * b x) +
      (∑ x, b x * A.adjMatrix (ZMod 2) x G) +
      (A.adjMatrix (ZMod 2) * Matrix.diagonal b * D +
        D * Matrix.diagonal b * A.adjMatrix (ZMod 2)) E G := by
  let M := A.adjMatrix (ZMod 2)
  let B := Matrix.diagonal b
  have hMEG : M E G = 0 := by
    simp [M, SimpleGraph.adjMatrix_apply, hEG]
  have hMB : (M * B) E G = 0 := by
    change (M * Matrix.diagonal b) E G = 0
    rw [Matrix.mul_diagonal]
    simp [hMEG]
  have hBM : (B * M) E G = 0 := by
    change (Matrix.diagonal b * M) E G = 0
    rw [Matrix.diagonal_mul]
    simp [hMEG]
  have hMBJ : (M * B * J) E G =
      ∑ x, M E x * b x := by
    change (M * Matrix.diagonal b * J) E G = _
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_diagonal]
    simp_rw [hJ]
    simp only [mul_one]
  have hJBM : (J * B * M) E G =
      ∑ x, b x * M x G := by
    change (J * Matrix.diagonal b * M) E G = _
    rw [Matrix.mul_apply]
    simp_rw [Matrix.mul_diagonal]
    simp_rw [hJ]
    simp only [one_mul]
  change (M * B * (M * M) + (M * M) * B * M) E G =
    (∑ x, M E x * b x) + (∑ x, b x * M x G) +
      (M * B * D + D * B * M) E G
  change M * M = D + J + 1 at hSquare
  rw [hSquare]
  simp only [mul_add, add_mul, Matrix.add_apply]
  simp only [mul_one, one_mul]
  rw [hMBJ, hJBM, hMB, hBM]
  abel

end Erdos85

#print axioms Erdos85.crossNeighborhood_flipMatrix_eq_starSums_add_defectCommutator
