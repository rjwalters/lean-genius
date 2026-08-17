import Proofs.Erdos85OrderSixtyFourRegularDeterminant
import Proofs.Erdos85ExcessEigenspace
import Proofs.Erdos85FrequencyPairTransport

/-! # The connected-defect branch at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If the 7-regular defect graph is preconnected, the adjacency matrix of
the putative order-64 graph is nonsingular over the reals. -/
theorem orderSixtyFour_adj_det_ne_zero_of_defect_preconnected
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hconn : (secondOrderDefectGraph G).Preconnected) :
    Matrix.det (G.adjMatrix ℝ) ≠ 0 := by
  let D := secondOrderDefectGraph G
  let A := G.adjMatrix ℝ
  let L := D.lapMatrix ℝ
  let J : Matrix (Fin 64) (Fin 64) ℝ := Matrix.of fun _ _ => 1
  have hkernel := orderSixtyFour_regular_defect_kernel
    G hfree hmin hcover
  have hreg : ∀ x : Fin 64, G.degree x = 8 := hkernel.1
  have hL :
      L = (7 : ℝ) • (1 : Matrix (Fin 64) (Fin 64) ℝ) -
        D.adjMatrix ℝ := by
    exact orderSixtyFour_defect_lapMatrix_eq G hfree hmin hcover
  have hsq : A * A = L + J := by
    have hz := hkernel.2.2.2
    have hr := congrArg
      (fun M : Matrix (Fin 64) (Fin 64) ℤ =>
        M.map (Int.castRingHom ℝ)) hz
    simp only [Matrix.map_mul, adjMatrix_map_intCast] at hr
    dsimp only [A, J]
    rw [hL]
    rw [hr]
    ext x y
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      FriendshipTheoremOQ01.onesMatrix, SimpleGraph.adjMatrix_apply,
      smul_eq_mul]
    split_ifs <;> norm_num
  intro hdet
  obtain ⟨v, hv0, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hsumL (w : Fin 64 → ℝ) : ∑ x, (L.mulVec w) x = 0 := by
    let u : Fin 64 → ℝ := fun _ => 1
    have hLones : L.mulVec u = 0 := by
      exact D.lapMatrix_mulVec_const_eq_zero
    have heq : u ⬝ᵥ (L.mulVec w) = 0 := by
      rw [Matrix.dotProduct_mulVec]
      have hsymm : L.transpose = L := (D.isSymm_lapMatrix ℝ).eq
      rw [← hsymm, Matrix.vecMul_transpose, hLones,
        zero_dotProduct]
    simpa [dotProduct, u] using heq
  have hsqv : (L + J).mulVec v = 0 := by
    rw [← hsq, ← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_zero]
  have hsumv : ∑ x, v x = 0 := by
    have hs := congrArg (fun w : Fin 64 → ℝ => ∑ x, w x) hsqv
    simp only [Matrix.add_mulVec, Pi.add_apply, Pi.zero_apply,
      Finset.sum_add_distrib, Finset.sum_const_zero] at hs
    rw [hsumL] at hs
    have hJ : ∀ x, (J.mulVec v) x = ∑ y, v y := by
      intro x
      simp [J, Matrix.mulVec, dotProduct]
    simp_rw [hJ] at hs
    simp only [Finset.sum_const] at hs
    norm_num at hs
    linarith
  have hJv : J.mulVec v = 0 := by
    funext x
    simp [J, Matrix.mulVec, dotProduct, hsumv]
  have hLv : L.mulVec v = 0 := by
    have := hsqv
    rw [Matrix.add_mulVec, hJv, add_zero] at this
    exact this
  have hconst : ∀ x : Fin 64, v x = v 0 := by
    intro x
    exact (D.lapMatrix_mulVec_eq_zero_iff_forall_reachable.mp hLv)
      x 0 (hconn x 0)
  have hvbase : v 0 = 0 := by
    have hsum : ∑ x : Fin 64, v x = 64 * v 0 := by
      calc
        ∑ x : Fin 64, v x = ∑ _x : Fin 64, v 0 :=
          Finset.sum_congr rfl fun x _ => hconst x
        _ = 64 * v 0 := by simp
    rw [hsum] at hsumv
    linarith
  apply hv0
  funext x
  rw [Pi.zero_apply, hconst x, hvbase]

end

end Erdos85
