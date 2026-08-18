import Proofs.Erdos85BinarySquareRegularParity

/-! # Pointwise action of the binary square-order adjacency square

The global identity `A² = (q-1)I + J - D` is exposed here as an exact
pointwise formula on arbitrary integer vectors.  This avoids repeatedly
unfolding matrix-vector application in signed-vector arguments.
-/

open SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- The square-order adjacency-square identity, evaluated pointwise on an
arbitrary integer vector. -/
theorem binarySquare_regular_adjMatrix_sq_mulVec_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q) (s : V → ℤ) (x : V) :
    ((G.adjMatrix ℤ * G.adjMatrix ℤ) *ᵥ s) x =
      ((q : ℤ) - 1) * s x + (∑ y, s y) -
        ∑ y ∈ (secondOrderDefectGraph G).neighborFinset x, s y := by
  rw [adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg (d := q),
    Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [SimpleGraph.adjMatrix_mulVec_apply]
  congr 2
  simp [FriendshipTheoremOQ01.onesMatrix, Matrix.mulVec, dotProduct]

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_adjMatrix_sq_mulVec_apply
