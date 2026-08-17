import Proofs.Erdos85OrderSixtyFourConnectedDefect
import Proofs.Erdos85SecondOrderQuotient

/-! # The disconnected-defect branch at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem sum_componentIndicator_eq_ncard
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableEq D.ConnectedComponent]
    (c : D.ConnectedComponent) :
    ∑ x : V, componentIndicator D c x = (c.supp.ncard : ℝ) := by
  simp only [componentIndicator]
  rw [Finset.sum_boole]
  norm_cast
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [SimpleGraph.ConnectedComponent.mem_supp_iff]

/-- Two distinct defect components give a nonzero, sum-zero vector in the
kernel of both the defect Laplacian and the all-ones matrix. -/
theorem orderSixtyFour_exists_balanced_component_kernel_vector
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hce : c ≠ e) :
    ∃ w : Fin 64 → ℝ, w ≠ 0 ∧
      ((secondOrderDefectGraph G).lapMatrix ℝ).mulVec w = 0 ∧
      (Matrix.of (fun _ _ => (1 : ℝ)) :
        Matrix (Fin 64) (Fin 64) ℝ).mulVec w = 0 := by
  classical
  let D := secondOrderDefectGraph G
  let sc : ℝ := c.supp.ncard
  let se : ℝ := e.supp.ncard
  let w := se • componentIndicator D c - sc • componentIndicator D e
  have hkernel := orderSixtyFour_regular_defect_kernel
    G hfree hmin hcover
  have hDreg : ∀ x : Fin 64, D.degree x = 7 := hkernel.2.2.1
  have hL :
      D.lapMatrix ℝ =
        (7 : ℝ) • (1 : Matrix (Fin 64) (Fin 64) ℝ) -
          D.adjMatrix ℝ :=
    orderSixtyFour_defect_lapMatrix_eq G hfree hmin hcover
  have hcEig := adjMatrix_mulVec_componentIndicator D 7 hDreg c
  have heEig := adjMatrix_mulVec_componentIndicator D 7 hDreg e
  have hcL : (D.lapMatrix ℝ).mulVec (componentIndicator D c) = 0 := by
    rw [hL, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, hcEig]
    norm_num
  have heL : (D.lapMatrix ℝ).mulVec (componentIndicator D e) = 0 := by
    rw [hL, Matrix.sub_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, heEig]
    norm_num
  have hsepos : 0 < se := by
    dsimp only [se]
    exact_mod_cast e.nonempty_supp.ncard_pos
  have hw0 : w ≠ 0 := by
    intro hw
    let x := componentRepresentative D c
    have hxc : D.connectedComponentMk x = c := by
      exact (SimpleGraph.ConnectedComponent.mem_supp_iff c x).mp
        (componentRepresentative_mem D c)
    have hxw := congrFun hw x
    simp [w, componentIndicator, hxc, hce] at hxw
    linarith
  have hwL : (D.lapMatrix ℝ).mulVec w = 0 := by
    dsimp only [w]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hcL, heL, smul_zero, smul_zero, sub_zero]
  have hsumw : ∑ x, w x = 0 := by
    dsimp only [w, sc, se]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [sum_componentIndicator_eq_ncard,
      sum_componentIndicator_eq_ncard]
    ring
  have hwJ : (Matrix.of (fun _ _ => (1 : ℝ)) :
      Matrix (Fin 64) (Fin 64) ℝ).mulVec w = 0 := by
    funext x
    simp [Matrix.mulVec, dotProduct, hsumw]
  refine ⟨w, hw0, ?_, hwJ⟩
  simpa [D] using hwL

/-- Consequently, the existence of two defect components forces the
original adjacency matrix to be singular. -/
theorem orderSixtyFour_adj_det_eq_zero_of_two_defect_components
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (c e : (secondOrderDefectGraph G).ConnectedComponent)
    (hce : c ≠ e) :
    Matrix.det (G.adjMatrix ℝ) = 0 := by
  let D := secondOrderDefectGraph G
  let A := G.adjMatrix ℝ
  let L := D.lapMatrix ℝ
  let J : Matrix (Fin 64) (Fin 64) ℝ := Matrix.of fun _ _ => 1
  obtain ⟨w, hw0, hwL, hwJ⟩ :=
    orderSixtyFour_exists_balanced_component_kernel_vector
      G hfree hmin hcover c e hce
  have hkernel := orderSixtyFour_regular_defect_kernel
    G hfree hmin hcover
  have hL :
      L = (7 : ℝ) • (1 : Matrix (Fin 64) (Fin 64) ℝ) -
        D.adjMatrix ℝ :=
    orderSixtyFour_defect_lapMatrix_eq G hfree hmin hcover
  have hsq : A * A = L + J := by
    have hz := hkernel.2.2.2
    have hr := congrArg
      (fun M : Matrix (Fin 64) (Fin 64) ℤ =>
        M.map (Int.castRingHom ℝ)) hz
    simp only [Matrix.map_mul, adjMatrix_map_intCast] at hr
    dsimp only [A, J]
    rw [hL, hr]
    ext x y
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      FriendshipTheoremOQ01.onesMatrix, SimpleGraph.adjMatrix_apply,
      smul_eq_mul]
    split_ifs <;> norm_num
  have hsqw : (A * A).mulVec w = 0 := by
    rw [hsq, Matrix.add_mulVec, hwL, hwJ, add_zero]
  have hdetSq : Matrix.det (A * A) = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨w, hw0, hsqw⟩
  rw [Matrix.det_mul] at hdetSq
  exact mul_self_eq_zero.mp hdetSq

/-- Equivalently, failure of defect preconnectedness forces adjacency
singularity. -/
theorem orderSixtyFour_adj_det_eq_zero_of_defect_not_preconnected
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hdisc : ¬ (secondOrderDefectGraph G).Preconnected) :
    Matrix.det (G.adjMatrix ℝ) = 0 := by
  rw [SimpleGraph.Preconnected] at hdisc
  push Not at hdisc
  obtain ⟨x, y, hxy⟩ := hdisc
  apply orderSixtyFour_adj_det_eq_zero_of_two_defect_components
    G hfree hmin hcover
    ((secondOrderDefectGraph G).connectedComponentMk x)
    ((secondOrderDefectGraph G).connectedComponentMk y)
  intro heq
  exact hxy (SimpleGraph.ConnectedComponent.exact heq)

end

end Erdos85
