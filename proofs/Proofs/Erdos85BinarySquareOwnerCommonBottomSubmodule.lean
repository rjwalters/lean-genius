import Proofs.Erdos85BinarySquareOwnerCommonBottomExact

/-!
# The common owner bottom as a canonical submodule

This packages the pointwise common-bottom equivalence as an equality of
submodules and transfers the exact adjacency-nullity formula to its finrank.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Intersection of all shifted owner-color kernels. -/
def binarySquareOwnerCommonBottomSubmodule
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ) :
    Submodule ℚ (V → ℚ) :=
  ⨅ c : (secondOrderDefectGraph G).ConnectedComponent,
    LinearMap.ker
      (((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℚ +
        (m c : ℚ) • (1 : Matrix V V ℚ)).mulVecLin)

/-- Membership is the simultaneous bottom-eigenvector condition. -/
theorem mem_binarySquareOwnerCommonBottomSubmodule_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (m : (secondOrderDefectGraph G).ConnectedComponent → ℕ)
    (v : V → ℚ) :
    v ∈ binarySquareOwnerCommonBottomSubmodule G m ↔
      ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
        ((componentOwnerGraph G
          (secondOrderDefectGraph G) c).adjMatrix ℚ).mulVec v =
            (-(m c : ℚ)) • v := by
  rw [binarySquareOwnerCommonBottomSubmodule]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hv c
    have hc := hv c
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hc
    simpa only [neg_smul] using eq_neg_of_add_eq_zero_left hc
  · intro hv c
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv c]
    simp

/-- The common shifted-owner kernel is exactly the ambient adjacency kernel. -/
theorem binarySquare_regular_ownerCommonBottomSubmodule_eq_adjKernel
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
    binarySquareOwnerCommonBottomSubmodule G m =
      LinearMap.ker (G.adjMatrix ℚ).mulVecLin := by
  ext v
  rw [mem_binarySquareOwnerCommonBottomSubmodule_iff, LinearMap.mem_ker]
  exact (binarySquare_regular_adj_mulVec_eq_zero_iff_forall_owner_bottom_rat
    G hfree hq hreg hcard m hm hsum v).symm

/-- Exact dimension of the common bottom eigenspace: one less than the number
of defect components. -/
theorem binarySquare_regular_finrank_ownerCommonBottomSubmodule
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
    (e₀ : (secondOrderDefectGraph G).ConnectedComponent) :
    Module.finrank ℚ (binarySquareOwnerCommonBottomSubmodule G m) =
      Fintype.card (secondOrderDefectGraph G).ConnectedComponent - 1 := by
  rw [binarySquare_regular_ownerCommonBottomSubmodule_eq_adjKernel
    G hfree hq hreg hcard m hm hsum]
  exact binarySquare_regular_finrank_adj_kernel_eq_card_components_sub_one
    G hfree hq hreg hcard e₀

end

end Erdos85
