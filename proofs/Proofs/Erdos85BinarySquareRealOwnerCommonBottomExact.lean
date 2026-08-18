import Proofs.Erdos85BinarySquareRealAdjacencyKernelExact
import Proofs.Erdos85BinarySquareOwnerCommonBottomExact
import Proofs.Erdos85BinarySquareTwoOwnerBottomBalance

/-! # Exact common owner bottom over the reals

The rational common-bottom identity is transported to `ℝ`, the coefficient
field used by the exact individual owner-bottom multiplicities.  This removes
the last scalar mismatch in the two-owner sector decomposition.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxRecDepth 10000

/-- Intersection of all real shifted-owner kernels. -/
def realBinarySquareOwnerCommonBottomSubmodule
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ) :
    Submodule ℝ (V → ℝ) :=
  ⨅ c : (secondOrderDefectGraph G).ConnectedComponent,
    realComponentOwnerBottomSubmodule G c (m c)

/-- The shifted owner matrices resolve `A²` over `ℝ`. -/
theorem binarySquare_regular_sum_shifted_componentOwnerGraph_adjMatrix_eq_sq_real
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (hreg : ∀ x, G.degree x = q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hsum : ∑ c, m c = q) :
    Finset.univ.sum (fun c :
        (secondOrderDefectGraph G).ConnectedComponent =>
      (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℝ +
        (m c : ℝ) • (1 : Matrix V V ℝ)) =
      G.adjMatrix ℝ * G.adjMatrix ℝ := by
  have hQ :=
    binarySquare_regular_sum_shifted_componentOwnerGraph_adjMatrix_eq_sq_rat
      G hfree hreg m hsum
  let f := Rat.castHom ℝ
  have hmap := congrArg (fun M : Matrix V V ℚ => M.map f) hQ
  have hadj (H : SimpleGraph V) [DecidableRel H.Adj] :
      (H.adjMatrix ℚ).map f = H.adjMatrix ℝ := by
    ext x y
    simp only [Matrix.map_apply, SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  have hterm (c : (secondOrderDefectGraph G).ConnectedComponent) :
      ((componentOwnerGraph G
          (secondOrderDefectGraph G) c).adjMatrix ℚ +
        (m c : ℚ) • (1 : Matrix V V ℚ)).map f =
      (componentOwnerGraph G
          (secondOrderDefectGraph G) c).adjMatrix ℝ +
        (m c : ℝ) • (1 : Matrix V V ℝ) := by
    ext x y
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
      Matrix.one_apply, SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  have hleft :
      (Finset.univ.sum (fun c :
          (secondOrderDefectGraph G).ConnectedComponent =>
        (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℚ +
          (m c : ℚ) • (1 : Matrix V V ℚ))).map f =
        Finset.univ.sum (fun c :
          (secondOrderDefectGraph G).ConnectedComponent =>
        (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℝ +
          (m c : ℝ) • (1 : Matrix V V ℝ)) := by
    calc
      _ = Finset.univ.sum (fun c =>
          ((componentOwnerGraph G
              (secondOrderDefectGraph G) c).adjMatrix ℚ +
            (m c : ℚ) • (1 : Matrix V V ℚ)).map f) := by
        ext x y
        simp [Matrix.map_apply, Matrix.sum_apply, f]
      _ = _ := by simp_rw [hterm]
  rw [hleft, Matrix.map_mul, hadj G] at hmap
  exact hmap

/-- Real owner-coordinate identity. -/
theorem binarySquare_regular_componentOwnerGraph_adjMatrix_eq_real
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
    (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℝ =
      G.adjMatrix ℝ *
          defectComponentDiagonalMatrix (K := ℝ)
            (secondOrderDefectGraph G) c * G.adjMatrix ℝ -
        (m_c : ℝ) • 1 := by
  have hQ := binarySquare_regular_componentOwnerGraph_adjMatrix_eq_rat
    G hfree hq hreg hcard c hc
  let f := Rat.castHom ℝ
  have hmap := congrArg (fun M : Matrix V V ℚ => M.map f) hQ
  have hO : ((componentOwnerGraph G
      (secondOrderDefectGraph G) c).adjMatrix ℚ).map f =
      (componentOwnerGraph G
        (secondOrderDefectGraph G) c).adjMatrix ℝ := by
    ext x y
    simp only [Matrix.map_apply, SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  have hA : (G.adjMatrix ℚ).map f = G.adjMatrix ℝ := by
    ext x y
    simp only [Matrix.map_apply, SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  have hP : (defectComponentDiagonalMatrix (K := ℚ)
      (secondOrderDefectGraph G) c).map f =
      defectComponentDiagonalMatrix (K := ℝ)
        (secondOrderDefectGraph G) c := by
    ext x y
    simp only [Matrix.map_apply, defectComponentDiagonalMatrix,
      Matrix.diagonal_apply]
    split_ifs <;> norm_num
  have hm : (((m_c : ℚ) • (1 : Matrix V V ℚ)).map f) =
      (m_c : ℝ) • (1 : Matrix V V ℝ) := by
    ext x y
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> norm_num
  rw [Matrix.map_sub f f.map_sub, Matrix.map_mul, Matrix.map_mul,
    hO, hA, hP, hm] at hmap
  exact hmap

/-- Every real adjacency-kernel vector belongs to every real owner bottom. -/
theorem binarySquare_regular_componentOwnerGraph_mulVec_of_adj_mulVec_eq_zero_real
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
    (v : V → ℝ) (hv : (G.adjMatrix ℝ).mulVec v = 0) :
    ((componentOwnerGraph G
      (secondOrderDefectGraph G) c).adjMatrix ℝ).mulVec v =
        (-(m_c : ℝ)) • v := by
  rw [binarySquare_regular_componentOwnerGraph_adjMatrix_eq_real
    G hfree hq hreg hcard c hc, Matrix.sub_mulVec,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv,
    Matrix.mulVec_zero, Matrix.mulVec_zero, Matrix.smul_mulVec,
    Matrix.one_mulVec]
  simp

/-- A real vector is in every owner bottom exactly when ambient adjacency
kills it. -/
theorem binarySquare_regular_adj_mulVec_eq_zero_iff_forall_owner_bottom_real
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (hsum : ∑ c, m c = q) (v : V → ℝ) :
    (G.adjMatrix ℝ).mulVec v = 0 ↔
      ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
        ((componentOwnerGraph G
          (secondOrderDefectGraph G) c).adjMatrix ℝ).mulVec v =
            (-(m c : ℝ)) • v := by
  constructor
  · intro hv c
    exact binarySquare_regular_componentOwnerGraph_mulVec_of_adj_mulVec_eq_zero_real
      G hfree hq hreg hcard c (hm c) v hv
  · intro hv
    have hshift (c : (secondOrderDefectGraph G).ConnectedComponent) :
        (((componentOwnerGraph G
            (secondOrderDefectGraph G) c).adjMatrix ℝ +
          (m c : ℝ) • (1 : Matrix V V ℝ)).mulVec v) = 0 := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv c]
      simp
    have hsq : (G.adjMatrix ℝ * G.adjMatrix ℝ).mulVec v = 0 := by
      rw [← binarySquare_regular_sum_shifted_componentOwnerGraph_adjMatrix_eq_sq_real
        G hfree hreg m hsum, Matrix.sum_mulVec]
      exact Finset.sum_eq_zero fun c _ => hshift c
    have hgram :
        ((G.adjMatrix ℝ).transpose * G.adjMatrix ℝ).mulVec v = 0 := by
      rw [G.isSymm_adjMatrix.eq]
      exact hsq
    have hmem : v ∈ LinearMap.ker
        ((G.adjMatrix ℝ).transpose * G.adjMatrix ℝ).mulVecLin := hgram
    have hmemA : v ∈ LinearMap.ker (G.adjMatrix ℝ).mulVecLin := by
      rw [← Matrix.ker_mulVecLin_transpose_mul_self (G.adjMatrix ℝ)]
      exact hmem
    exact hmemA

/-- The common real shifted-owner kernel is exactly the real ambient adjacency
kernel. -/
theorem binarySquare_regular_realOwnerCommonBottomSubmodule_eq_adjKernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (hsum : ∑ c, m c = q) :
    realBinarySquareOwnerCommonBottomSubmodule G m =
      LinearMap.ker (G.adjMatrix ℝ).mulVecLin := by
  ext v
  simp only [realBinarySquareOwnerCommonBottomSubmodule,
    Submodule.mem_iInf, realComponentOwnerBottomSubmodule,
    LinearMap.mem_ker, Matrix.mulVecLin_apply]
  rw [binarySquare_regular_adj_mulVec_eq_zero_iff_forall_owner_bottom_real
    G hfree hq hreg hcard m hm hsum v]
  constructor
  · intro hv c
    have hc := hv c
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hc
    simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hc
  · intro hv c
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv c]
    simp

/-- Exact dimension of the common real owner bottom. -/
theorem binarySquare_regular_finrank_realOwnerCommonBottomSubmodule
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (hsum : ∑ c, m c = q) :
    Module.finrank ℝ (realBinarySquareOwnerCommonBottomSubmodule G m) =
      Fintype.card (secondOrderDefectGraph G).ConnectedComponent - 1 := by
  rw [binarySquare_regular_realOwnerCommonBottomSubmodule_eq_adjKernel
    G hfree hq hreg hcard m hm hsum]
  exact binarySquare_regular_finrank_adj_kernel_real
    G hfree hq hreg hcard

/-- **Exact two-owner decomposition.**  When there are exactly two defect
components, their real owner-bottom spaces intersect in the one-dimensional
ambient adjacency kernel and jointly span a codimension-one subspace. -/
theorem binarySquare_regular_twoOwner_bottom_inter_inf_and_sup_finrank
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (hm : ∀ c, c.supp.ncard = q * m c)
    (hsum : ∑ c, m c = q)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 2)
    (a b : (secondOrderDefectGraph G).ConnectedComponent) (hab : a ≠ b) :
    Module.finrank ℝ
        ↥(realComponentOwnerBottomSubmodule G a (m a) ⊓
          realComponentOwnerBottomSubmodule G b (m b)) = 1 ∧
      Module.finrank ℝ
        ↥(realComponentOwnerBottomSubmodule G a (m a) ⊔
          realComponentOwnerBottomSubmodule G b (m b)) = q * q - 1 := by
  let E : (secondOrderDefectGraph G).ConnectedComponent ≃ Fin 2 :=
    Fintype.equivFinOfCardEq hcount
  have hcover (c : (secondOrderDefectGraph G).ConnectedComponent) :
      c = a ∨ c = b := by
    have habE : E a ≠ E b := fun h => hab (E.injective h)
    have hcE : E c = E a ∨ E c = E b := by
      omega
    rcases hcE with h | h
    · exact Or.inl (E.injective h)
    · exact Or.inr (E.injective h)
  have hcommonEq :
      realBinarySquareOwnerCommonBottomSubmodule G m =
        realComponentOwnerBottomSubmodule G a (m a) ⊓
          realComponentOwnerBottomSubmodule G b (m b) := by
    ext v
    simp only [realBinarySquareOwnerCommonBottomSubmodule,
      Submodule.mem_iInf, Submodule.mem_inf]
    constructor
    · intro hv
      exact ⟨hv a, hv b⟩
    · rintro ⟨ha, hb⟩ c
      rcases hcover c with rfl | rfl
      · exact ha
      · exact hb
  have hinf : Module.finrank ℝ
      ↥(realComponentOwnerBottomSubmodule G a (m a) ⊓
        realComponentOwnerBottomSubmodule G b (m b)) = 1 := by
    rw [← hcommonEq,
      binarySquare_regular_finrank_realOwnerCommonBottomSubmodule
        G hfree hq hreg hcard m hm hsum, hcount]
  have hbalance :=
    binarySquare_regular_twoOwner_bottom_sup_inf_finrank_add
      G hfree hq hreg hcard a b (hm a) (hm b) ?_
  · constructor
    · exact hinf
    · rw [hinf] at hbalance
      omega
  · have hsum' := hsum
    rw [show (Finset.univ : Finset
        (secondOrderDefectGraph G).ConnectedComponent) = {a, b} by
      ext c
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
        true_iff]
      exact hcover c] at hsum'
    simpa [hab] using hsum'

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_finrank_realOwnerCommonBottomSubmodule
#print axioms Erdos85.binarySquare_regular_twoOwner_bottom_inter_inf_and_sup_finrank
