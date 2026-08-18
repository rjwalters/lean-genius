import Proofs.Erdos85DefectComponentBlockCommute
import Proofs.Erdos85OrderSixtyFourSevenComponent

/-! # The exterior Gram term on a defect-component block -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Restricting a global matrix-square identity to a diagonal block produces
an additional cross-block product. -/
theorem toBlock_sq_add_cross_eq_of_sq_eq
    {K V : Type*} [CommRing K] [Fintype V] [DecidableEq V]
    (A D : Matrix V V K) (J : Matrix V V K) (a : K)
    (hsq : A * A = a • (1 : Matrix V V K) + J - D)
    (p : V → Prop) [DecidablePred p] :
    A.toBlock p p * A.toBlock p p +
        A.toBlock p (fun x ↦ ¬p x) *
          A.toBlock (fun x ↦ ¬p x) p =
      a • (1 : Matrix {x // p x} {x // p x} K) +
        J.toBlock p p - D.toBlock p p := by
  have hblock := congrArg (fun M ↦ M.toBlock p p) hsq
  rw [Matrix.toBlock_mul_eq_add p p p A A] at hblock
  calc
    _ = (a • (1 : Matrix V V K) + J - D).toBlock p p := hblock
    _ = _ := by
      ext i j
      by_cases hij : i = j
      · simp [Matrix.toBlock_apply, hij]
      · have hv : (i.1 : V) ≠ j.1 := fun h ↦ hij (Subtype.ext h)
        simp [Matrix.toBlock_apply, hij, hv]

/-- On a defect component of an order-64 candidate, the square of the
internal ambient adjacency block plus the exterior incidence Gram product
is `7I + J - D_c`.  In particular, replacing `D_c` by `7I-A_c²` would omit
the displayed cross term. -/
theorem orderSixtyFour_defectComponent_internal_sq_add_exteriorGram
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
    (G.induce c.supp).adjMatrix ℤ * (G.induce c.supp).adjMatrix ℤ +
        (G.adjMatrix ℤ).toBlock p (fun x ↦ ¬p x) *
          (G.adjMatrix ℤ).toBlock (fun x ↦ ¬p x) p =
      7 • (1 : Matrix c.supp c.supp ℤ) +
        FriendshipTheoremOQ01.onesMatrix c.supp -
          ((secondOrderDefectGraph G).induce c.supp).adjMatrix ℤ := by
  classical
  let D := secondOrderDefectGraph G
  let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
  have hreg := orderSixtyFour_regular_of_tightCover G hfree hmin hcover
  have hsq := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular
    G hfree hreg
  have hblock := toBlock_sq_add_cross_eq_of_sq_eq
    (G.adjMatrix ℤ) (D.adjMatrix ℤ)
    (FriendshipTheoremOQ01.onesMatrix (Fin 64)) 7 (by
      simpa using hsq) p
  have hGblock : (G.adjMatrix ℤ).toBlock p p =
      (G.induce c.supp).adjMatrix ℤ := by
    ext i j
    simp [p, Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply]
  have hDblock : (D.adjMatrix ℤ).toBlock p p =
      (D.induce c.supp).adjMatrix ℤ := by
    ext i j
    simp [p, Matrix.toBlock_apply, SimpleGraph.adjMatrix_apply]
  have hJblock :
      (FriendshipTheoremOQ01.onesMatrix (Fin 64)).toBlock p p =
        FriendshipTheoremOQ01.onesMatrix c.supp := by
    ext i j
    simp [p, Matrix.toBlock_apply, FriendshipTheoremOQ01.onesMatrix]
  rw [hGblock, hDblock, hJblock] at hblock
  exact hblock

end

end Erdos85
