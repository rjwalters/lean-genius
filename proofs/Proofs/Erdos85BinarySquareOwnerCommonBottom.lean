import Proofs.Erdos85BinarySquareComponentConstantKernelDimension

/-!
# The ambient kernel is a common bottom eigenspace of every owner color

The identity `O_c = A P_c A - m_c I` immediately implies that every vector
annihilated by ambient adjacency is a `-m_c` eigenvector of every owner-color
graph.  Combining this inclusion with the component-constant kernel dimension
gives a simultaneous bottom-eigenvalue multiplicity bound.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Rational cast of the owner-coordinate Gram identity. -/
theorem binarySquare_regular_componentOwnerGraph_adjMatrix_eq_rat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (hc : c.supp.ncard = q * m_c) :
    (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℚ =
      G.adjMatrix ℚ *
          defectComponentDiagonalMatrix (K := ℚ)
            (secondOrderDefectGraph G) c * G.adjMatrix ℚ -
        (m_c : ℚ) • 1 := by
  have hZ := binarySquare_regular_componentOwnerGraph_adjMatrix_eq
    G hfree hq hreg hcard c hc
  have hmap := congrArg (fun M : Matrix V V ℤ =>
    M.map (Int.castRingHom ℚ)) hZ
  have hO : ((componentOwnerGraph G
      (secondOrderDefectGraph G) c).adjMatrix ℤ).map
        (Int.castRingHom ℚ) =
      (componentOwnerGraph G
        (secondOrderDefectGraph G) c).adjMatrix ℚ := by
    ext x y
    simp [SimpleGraph.adjMatrix_apply]
  have hA : (G.adjMatrix ℤ).map (Int.castRingHom ℚ) =
      G.adjMatrix ℚ := by
    ext x y
    simp [SimpleGraph.adjMatrix_apply]
  have hP : (defectComponentDiagonalMatrix (K := ℤ)
      (secondOrderDefectGraph G) c).map (Int.castRingHom ℚ) =
      defectComponentDiagonalMatrix (K := ℚ)
        (secondOrderDefectGraph G) c := by
    ext x y
    by_cases hxy : x = y <;>
      simp [defectComponentDiagonalMatrix, Matrix.diagonal_apply, hxy]
  have hm : (((m_c : ℤ) • (1 : Matrix V V ℤ)).map
      (Int.castRingHom ℚ)) = (m_c : ℚ) • (1 : Matrix V V ℚ) := by
    ext x y
    by_cases hxy : x = y <;>
      simp [zsmul_eq_mul, Matrix.intCast_apply, Matrix.natCast_apply,
        Matrix.one_apply,
        Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, hxy]
  rw [Matrix.map_sub (Int.castRingHom ℚ)
      (Int.castRingHom ℚ).map_sub,
    Matrix.map_mul, Matrix.map_mul, hO, hA, hP, hm] at hmap
  exact hmap

/-- Every ambient adjacency-kernel vector is a bottom eigenvector of every
owner color. -/
theorem binarySquare_regular_componentOwnerGraph_mulVec_of_adj_mulVec_eq_zero_rat
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (hc : c.supp.ncard = q * m_c)
    (v : V → ℚ) (hv : (G.adjMatrix ℚ).mulVec v = 0) :
    ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℚ).mulVec v =
      (-(m_c : ℚ)) • v := by
  rw [binarySquare_regular_componentOwnerGraph_adjMatrix_eq_rat
    G hfree hq hreg hcard c hc, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  simp

/-- Inclusion of the ambient adjacency kernel into the shifted owner-color
kernel. -/
def binarySquareAdjKernelToOwnerBottomKernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (hc : c.supp.ncard = q * m_c) :
    LinearMap.ker (G.adjMatrix ℚ).mulVecLin →ₗ[ℚ]
      LinearMap.ker
        (((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℚ +
          (m_c : ℚ) • 1).mulVecLin) where
  toFun v := ⟨v.1, by
    rw [LinearMap.mem_ker]
    change (((componentOwnerGraph G
      (secondOrderDefectGraph G) c).adjMatrix ℚ) +
        (m_c : ℚ) • 1).mulVec v.1 = 0
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      binarySquare_regular_componentOwnerGraph_mulVec_of_adj_mulVec_eq_zero_rat
        G hfree hq hreg hcard c hc v.1 v.2]
    simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem binarySquareAdjKernelToOwnerBottomKernel_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (hc : c.supp.ncard = q * m_c) :
    Function.Injective
      (binarySquareAdjKernelToOwnerBottomKernel
        G hfree hq hreg hcard c hc) := by
  intro u v huv
  apply Subtype.ext
  exact congrArg (fun z => z.1) huv

/-- Every owner color has bottom-eigenvalue multiplicity at least one less
than the number of defect components.  More strongly, the same ambient
kernel realizes all these bottom eigenspaces simultaneously. -/
theorem binarySquare_regular_card_components_sub_one_le_finrank_owner_bottom
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e₀ c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (hc : c.supp.ncard = q * m_c) :
    Fintype.card (secondOrderDefectGraph G).ConnectedComponent - 1 ≤
      Module.finrank ℚ (LinearMap.ker
        (((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℚ +
          (m_c : ℚ) • 1).mulVecLin)) := by
  have hA :=
    binarySquare_regular_card_components_sub_one_le_finrank_adj_kernel
      G hfree hq hreg hcard e₀
  have hinj := binarySquareAdjKernelToOwnerBottomKernel_injective
    G hfree hq hreg hcard c hc
  exact hA.trans (LinearMap.finrank_le_finrank_of_injective hinj)

end

end Erdos85
