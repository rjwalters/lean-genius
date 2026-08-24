import Proofs.Erdos85BinarySquareConnectedOwnerComplement

/-!
# The blind sector as a dense complement kernel

At binary square order the ambient square is literally `qI` plus the
adjacency matrix of the complement of the second-order defect graph.  Thus
the `A² = q` blind sector has an entrywise description: every coordinate
has zero sum over its complement-defect neighborhood.  This is the
coordinate interface needed by any small-multiplicity argument.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Exact uncentered ambient/complement coupling at square order. -/
theorem binarySquare_regular_adjMatrix_sq_eq_q_identity_add_defectCompl
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q) :
    G.adjMatrix ℚ * G.adjMatrix ℚ =
      (q : ℚ) • (1 : Matrix V V ℚ) +
        (secondOrderDefectGraph G)ᶜ.adjMatrix ℚ := by
  have hsq := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular_rat
    G hfree hreg
  rw [hsq]
  ext x y
  by_cases hxy : x = y
  · subst y
    simp [ratOnesMatrix, SimpleGraph.adjMatrix_apply]
  · by_cases hD : (secondOrderDefectGraph G).Adj x y
    · simp [ratOnesMatrix,
        SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj, hxy, hD]
    · simp [ratOnesMatrix,
        SimpleGraph.adjMatrix_apply, SimpleGraph.compl_adj, hxy, hD]

/-- The ambient `A²-qI` operator is exactly dense complement-defect
adjacency. -/
theorem binarySquare_regular_adjMatrix_sq_sub_q_identity_eq_defectCompl
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q) :
    G.adjMatrix ℚ * G.adjMatrix ℚ -
        (q : ℚ) • (1 : Matrix V V ℚ) =
      (secondOrderDefectGraph G)ᶜ.adjMatrix ℚ := by
  rw [binarySquare_regular_adjMatrix_sq_eq_q_identity_add_defectCompl
    G hfree hreg]
  abel

/-- Exact kernel identification for the `mu=-1` / `A²=q` blind sector. -/
theorem binarySquare_regular_blindSector_ker_eq_defectCompl_ker
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q) :
    LinearMap.ker
        (G.adjMatrix ℚ * G.adjMatrix ℚ -
          (q : ℚ) • (1 : Matrix V V ℚ)).mulVecLin =
      LinearMap.ker ((secondOrderDefectGraph G)ᶜ.adjMatrix ℚ).mulVecLin := by
  rw [binarySquare_regular_adjMatrix_sq_sub_q_identity_eq_defectCompl
    G hfree hreg]

/-- Coordinate form of the blind-sector kernel: the sum over every dense
complement-defect neighborhood vanishes. -/
theorem mem_binarySquare_regular_blindSector_ker_iff_complNeighbor_sum_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q) (z : V → ℚ) :
    z ∈ LinearMap.ker
        (G.adjMatrix ℚ * G.adjMatrix ℚ -
          (q : ℚ) • (1 : Matrix V V ℚ)).mulVecLin ↔
      ∀ x : V,
        ∑ y ∈ (secondOrderDefectGraph G)ᶜ.neighborFinset x, z y = 0 := by
  rw [binarySquare_regular_blindSector_ker_eq_defectCompl_ker G hfree hreg]
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hz x
    have hx := congrFun hz x
    simpa [SimpleGraph.adjMatrix_mulVec_apply] using hx
  · intro hz
    funext x
    simpa [SimpleGraph.adjMatrix_mulVec_apply] using hz x

end

end Erdos85

#print axioms
  Erdos85.binarySquare_regular_adjMatrix_sq_eq_q_identity_add_defectCompl
#print axioms
  Erdos85.binarySquare_regular_adjMatrix_sq_sub_q_identity_eq_defectCompl
#print axioms Erdos85.binarySquare_regular_blindSector_ker_eq_defectCompl_ker
#print axioms
  Erdos85.mem_binarySquare_regular_blindSector_ker_iff_complNeighbor_sum_zero
