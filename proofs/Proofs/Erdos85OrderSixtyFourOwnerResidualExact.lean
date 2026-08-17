import Proofs.Erdos85BinarySquareOwnerBottomMultiplicity
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Exact owner residual at order 64

For a size-16 defect component, the degree-16 factor left after removing the
48-dimensional owner bottom eigenspace is exactly the shifted characteristic
polynomial of the component incidence self-Gram.
-/

open SimpleGraph Polynomial

namespace Erdos85

noncomputable section

/-- **Exact owner residual polynomial.**  If `c` has order sixteen, then the
owner characteristic polynomial is `(X+2)^48` times the characteristic
polynomial of `L(G[c])+J`, shifted by `X ↦ X+2`. -/
theorem orderSixtyFour_sizeSixteen_componentOwnerGraph_charpoly_exact
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (hreg : ∀ x, G.degree x = 8)
    (hcard : Fintype.card V = 64)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc : c.supp.ncard = 16) :
    ((componentOwnerGraph G
      (secondOrderDefectGraph G) c).adjMatrix ℝ).charpoly =
      (X + C (2 : ℝ)) ^ 48 *
        (((secondOrderDefectGraph G).induce c.supp).lapMatrix ℝ +
          Matrix.of (fun _ _ => (1 : ℝ))).charpoly.comp
            (X + C (2 : ℝ)) := by
  let I := realDefectComponentNeighborIncidenceMatrix G c
  let O := (componentOwnerGraph G
    (secondOrderDefectGraph G) c).adjMatrix ℝ
  let Q := ((secondOrderDefectGraph G).induce c.supp).lapMatrix ℝ +
    Matrix.of (fun _ _ => (1 : ℝ))
  have hcs : Fintype.card c.supp = 16 := by
    rw [Set.fintypeCard_eq_ncard]
    exact hc
  have hle : Fintype.card c.supp ≤ Fintype.card V := by omega
  have hrect := Matrix.charpoly_mul_comm_of_le I I.transpose hle
  have hrow : I * I.transpose = O +
      (2 : ℝ) • (1 : Matrix V V ℝ) := by
    simpa [I, O] using
      realDefectComponentNeighborIncidenceMatrix_mul_transpose_eq_ownerShift
        G hfree (q := 8) (by omega) hreg (by simpa using hcard) c
          (m_c := 2) (by simpa using hc)
  have hcol : I.transpose * I = Q := by
    simpa [I, Q] using
      transpose_realDefectComponentNeighborIncidenceMatrix_mul_self_eq
        G hfree (q := 8) (by omega) hreg (by simpa using hcard) c
  rw [hrow, hcol, hcard, hcs] at hrect
  norm_num at hrect
  have hadd : O + (2 : ℝ) • (1 : Matrix V V ℝ) =
      O - Matrix.scalar V (-2 : ℝ) := by
    ext x y
    by_cases hxy : x = y <;> simp [hxy]
  rw [hadd, Matrix.charpoly_sub_scalar] at hrect
  have hcompose := congrArg
    (fun p : ℝ[X] => p.comp (X + C (2 : ℝ))) hrect
  rw [Polynomial.mul_comp, Polynomial.pow_comp] at hcompose
  have hinner :
      (X + C (-2 : ℝ)).comp (X + C (2 : ℝ)) = X := by simp
  rw [Polynomial.comp_assoc, hinner, Polynomial.comp_X] at hcompose
  simpa [O, Q] using hcompose

end

end Erdos85
