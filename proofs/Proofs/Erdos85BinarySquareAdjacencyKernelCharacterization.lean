import Proofs.Erdos85BinarySquareAdjacencyNullity

/-!
# Pointwise characterization of the square-order adjacency kernel

At regular square order, an adjacency-kernel vector is exactly a function
which is constant on every defect component and whose total coordinate sum is
zero.  Thus the previously constructed component-constant kernel is the whole
zero eigenspace, not merely a subspace of the correct dimension.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Complete zero-eigenspace description.** -/
theorem binarySquare_regular_adjMatrix_mulVec_eq_zero_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (v : V → ℝ) :
    (G.adjMatrix ℝ).mulVec v = 0 ↔
      (∀ x y, (secondOrderDefectGraph G).Reachable x y → v x = v y) ∧
        ∑ x, v x = 0 := by
  let A := G.adjMatrix ℝ
  let D := secondOrderDefectGraph G
  let L := D.lapMatrix ℝ
  let J := realOnesMatrix V
  let C := binarySquareCenteredAdjacencyMatrix G q
  have hA2 : A * A = L + J := by
    have hsq := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular_real
      G hfree hreg
    have hL := binarySquare_regular_defect_lapMatrix_eq
      G hfree hq hreg hcard
    dsimp [A, D, L, J]
    rw [hL, hsq]
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    module
  have hAT : A.transpose = A := G.isSymm_adjMatrix.eq
  have hJ (w : V → ℝ) : J.mulVec w = (∑ x, w x) • Function.const V 1 := by
    funext x
    simp [J, realOnesMatrix, Matrix.mulVec, dotProduct]
  constructor
  · intro hAv
    have hCv : C.mulVec v = -(J.mulVec v) := by
      dsimp [C]
      rw [binarySquareCenteredAdjacencyMatrix,
        Matrix.sub_mulVec, Matrix.smul_mulVec, hAv]
      simp [J]
    have hsumC := binarySquareCenteredAdjacencyMatrix_coordinateSum_eq_zero
      G hreg hcard v
    rw [hCv, hJ] at hsumC
    have hcardPos : (0 : ℝ) < Fintype.card V := by
      rw [hcard]
      positivity
    have hsumv : ∑ x, v x = 0 := by
      simp only [Pi.neg_apply, Pi.smul_apply, Function.const_apply,
        smul_eq_mul, mul_one, Finset.sum_neg_distrib,
        Finset.sum_const, nsmul_eq_mul] at hsumC
      rw [Finset.card_univ] at hsumC
      nlinarith
    have hJv : J.mulVec v = 0 := by rw [hJ, hsumv]; simp
    have hLv : L.mulVec v = 0 := by
      have hv := congrArg (fun M : Matrix V V ℝ => M.mulVec v) hA2
      rw [← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_zero,
        Matrix.add_mulVec, hJv, add_zero] at hv
      exact hv.symm
    refine ⟨?_, hsumv⟩
    exact D.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp hLv
  · rintro ⟨hconst, hsumv⟩
    have hLv : L.mulVec v = 0 :=
      D.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mpr hconst
    have hJv : J.mulVec v = 0 := by rw [hJ, hsumv]; simp
    have hA2v : (A * A).mulVec v = 0 := by
      rw [hA2, Matrix.add_mulVec, hLv, hJv, add_zero]
    have hgram : (A.transpose * A).mulVec v = 0 := by
      rw [hAT]
      exact hA2v
    have hmem : v ∈ LinearMap.ker (A.transpose * A).mulVecLin := by
      exact hgram
    have hmemA : v ∈ LinearMap.ker A.mulVecLin := by
      rw [← Matrix.ker_mulVecLin_transpose_mul_self A]
      exact hmem
    exact hmemA

end

end Erdos85
