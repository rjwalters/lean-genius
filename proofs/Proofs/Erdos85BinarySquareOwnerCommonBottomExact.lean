import Proofs.Erdos85BinarySquareExactAdjacencyKernel
import Proofs.Erdos85BinarySquareOwnerCommonBottom
import Proofs.Erdos85SymmetricSectorFactorization

/-!
# Exact common bottom eigenspace of the owner colors

The ambient adjacency kernel is not only contained in every shifted owner
kernel.  It is their exact common intersection.  Indeed, the shifted owner
matrices sum to the square of ambient adjacency, and a symmetric rational
matrix has the same kernel as its square.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The shifted owner-color matrices resolve the square of ambient adjacency
over `ℚ`. -/
theorem binarySquare_regular_sum_shifted_componentOwnerGraph_adjMatrix_eq_sq_rat
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
    Finset.univ.sum (fun c : (secondOrderDefectGraph G).ConnectedComponent =>
        (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℚ +
          (m c : ℚ) • (1 : Matrix V V ℚ)) =
      G.adjMatrix ℚ * G.adjMatrix ℚ := by
  have hownersZ :=
    sum_componentOwnerGraph_adjMatrix_eq_ones_sub_one_sub_secondOrderDefect
      G hfree
  have howners := congrArg (fun M : Matrix V V ℤ =>
    M.map (Int.castRingHom ℚ)) hownersZ
  have hownersQ :
      (∑ c : (secondOrderDefectGraph G).ConnectedComponent,
          (componentOwnerGraph G
            (secondOrderDefectGraph G) c).adjMatrix ℚ) =
        ratOnesMatrix V - 1 -
          (secondOrderDefectGraph G).adjMatrix ℚ := by
    ext x y
    have hxy := congrFun (congrFun howners x) y
    simpa [Matrix.map_apply, Matrix.sum_apply, Matrix.sub_apply,
      Matrix.one_apply, FriendshipTheoremOQ01.onesMatrix, ratOnesMatrix,
      SimpleGraph.adjMatrix_apply] using hxy
  have hmQ : ∑ c : (secondOrderDefectGraph G).ConnectedComponent,
      (m c : ℚ) = q := by
    exact_mod_cast hsum
  rw [Finset.sum_add_distrib, hownersQ]
  rw [← Finset.sum_smul, hmQ]
  rw [adjMatrix_sq_eq_sub_secondOrderDefect_of_regular_rat G hfree hreg]
  module

/-- A vector is killed by ambient adjacency exactly when it is a bottom
eigenvector for every owner color.  Thus the common bottom eigenspace has no
directions beyond the component-constant ambient kernel. -/
theorem binarySquare_regular_adj_mulVec_eq_zero_iff_forall_owner_bottom_rat
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
    (hsum : ∑ c, m c = q) (v : V → ℚ) :
    (G.adjMatrix ℚ).mulVec v = 0 ↔
      ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
        ((componentOwnerGraph G
          (secondOrderDefectGraph G) c).adjMatrix ℚ).mulVec v =
            (-(m c : ℚ)) • v := by
  constructor
  · intro hv c
    exact binarySquare_regular_componentOwnerGraph_mulVec_of_adj_mulVec_eq_zero_rat
      G hfree hq hreg hcard c (hm c) v hv
  · intro hv
    have hshift (c : (secondOrderDefectGraph G).ConnectedComponent) :
        (((componentOwnerGraph G
            (secondOrderDefectGraph G) c).adjMatrix ℚ +
          (m c : ℚ) • (1 : Matrix V V ℚ)).mulVec v) = 0 := by
      rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv c]
      simp
    have hsq : (G.adjMatrix ℚ * G.adjMatrix ℚ).mulVec v = 0 := by
      rw [← binarySquare_regular_sum_shifted_componentOwnerGraph_adjMatrix_eq_sq_rat
        G hfree hreg m hsum, Matrix.sum_mulVec]
      exact Finset.sum_eq_zero fun c _ => hshift c
    exact matrix_mulVec_eq_zero_of_isSymm_of_sq_mulVec_eq_zero
      G.isSymm_adjMatrix hsq

end

end Erdos85
