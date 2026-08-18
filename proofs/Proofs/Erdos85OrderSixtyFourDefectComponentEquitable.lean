import Proofs.Erdos85OrderSixtyFourDisconnectedDefect

/-! # Equitable defect components at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem real_matrix_mulVec_eq_zero_of_isSymm_of_sq_mulVec_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {M : Matrix V V ℝ} (hM : M.IsSymm) {v : V → ℝ}
    (hzero : (M * M).mulVec v = 0) :
    M.mulVec v = 0 := by
  have hzero' : (M.transpose * M).mulVec v = 0 := by
    rw [hM]
    exact hzero
  have hv : v ∈ LinearMap.ker (M.transpose * M).mulVecLin :=
    LinearMap.mem_ker.mpr hzero'
  rw [Matrix.ker_mulVecLin_transpose_mul_self M] at hv
  simpa [LinearMap.mem_ker] using hv

/-- Every defect-component indicator is sent by the ambient adjacency matrix
to the constant vector whose value is one eighth of the component order.  We
state the identity without division so that its integral counting consequence
is immediate. -/
theorem orderSixtyFour_eight_smul_adj_componentIndicator
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    (8 : ℝ) • (G.adjMatrix ℝ).mulVec
        (componentIndicator (secondOrderDefectGraph G) c) =
      (c.supp.ncard : ℝ) • (fun _ : Fin 64 => (1 : ℝ)) := by
  classical
  let D := secondOrderDefectGraph G
  let A := G.adjMatrix ℝ
  let L := D.lapMatrix ℝ
  let J : Matrix (Fin 64) (Fin 64) ℝ := Matrix.of fun _ _ => 1
  let u : Fin 64 → ℝ := fun _ => 1
  let n : ℝ := c.supp.ncard
  let w : Fin 64 → ℝ := (64 : ℝ) • componentIndicator D c - n • u
  have hkernel := orderSixtyFour_regular_defect_kernel G hfree hmin hcover
  have hreg : ∀ x : Fin 64, G.degree x = 8 := hkernel.1
  have hDreg : ∀ x : Fin 64, D.degree x = 7 := hkernel.2.2.1
  have hL : L = (7 : ℝ) • (1 : Matrix (Fin 64) (Fin 64) ℝ) -
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
  have hLic : L.mulVec (componentIndicator D c) = 0 := by
    rw [hL, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      adjMatrix_mulVec_componentIndicator D 7 hDreg c]
    norm_num
  have hLu : L.mulVec u = 0 := by
    exact D.lapMatrix_mulVec_const_eq_zero
  have hJic : J.mulVec (componentIndicator D c) = n • u := by
    funext x
    simp [J, n, u, Matrix.mulVec, dotProduct,
      sum_componentIndicator_eq_ncard]
  have hJu : J.mulVec u = (64 : ℝ) • u := by
    funext x
    simp [J, u, Matrix.mulVec, dotProduct]
  have hsqw : (A * A).mulVec w = 0 := by
    rw [hsq, Matrix.add_mulVec]
    dsimp only [w]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hLic, hLu, Matrix.mulVec_sub, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hJic, hJu]
    module
  have hAw : A.mulVec w = 0 := by
    apply real_matrix_mulVec_eq_zero_of_isSymm_of_sq_mulVec_eq_zero
      G.isSymm_adjMatrix
    exact hsqw
  have hAu : A.mulVec u = (8 : ℝ) • u := by
    dsimp only [A, u]
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    simp [hreg x, G.card_neighborFinset_eq_degree]
  dsimp only [w] at hAw
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, hAu] at hAw
  dsimp only [A, D, n, u] at hAw ⊢
  funext x
  have hx := congrFun hAw x
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at hx ⊢
  linarith

/-- Consequently every vertex has exactly `|c| / 8` ambient neighbors in a
fixed defect component `c`; equivalently, eight times that count is `|c|`. -/
theorem orderSixtyFour_eight_mul_componentNeighborFinset_card
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent) (x : Fin 64) :
    8 * (componentNeighborFinset G (secondOrderDefectGraph G) c x).card =
      c.supp.ncard := by
  classical
  have h := congrFun
    (orderSixtyFour_eight_smul_adj_componentIndicator
      G hfree hmin hcover c) x
  simp only [Pi.smul_apply, smul_eq_mul] at h
  have hcount :
      (G.adjMatrix ℝ).mulVec
          (componentIndicator (secondOrderDefectGraph G) c) x =
        ((componentNeighborFinset G (secondOrderDefectGraph G) c x).card : ℝ) := by
    rw [SimpleGraph.adjMatrix_mulVec_apply]
    simp only [componentIndicator, componentNeighborFinset]
    rw [← Finset.sum_filter]
    simp
  rw [hcount] at h
  norm_num at h
  exact_mod_cast h

/-- Every connected component of the seven-regular defect graph has order
divisible by eight. -/
theorem orderSixtyFour_eight_dvd_defect_component_order
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    8 ∣ c.supp.ncard := by
  classical
  let x := componentRepresentative (secondOrderDefectGraph G) c
  refine ⟨(componentNeighborFinset G (secondOrderDefectGraph G) c x).card, ?_⟩
  exact (orderSixtyFour_eight_mul_componentNeighborFinset_card
    G hfree hmin hcover c x).symm

/-- The entire component quotient is forced by the component orders: every
row is the same, and eight times the entry in column `c` is `|c|`. -/
theorem orderSixtyFour_eight_mul_componentQuotientMatrix_apply
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (e c : (secondOrderDefectGraph G).ConnectedComponent) :
    8 * componentQuotientMatrix G (secondOrderDefectGraph G) e c =
      c.supp.ncard := by
  classical
  change 8 * (componentNeighborFinset G (secondOrderDefectGraph G) c
    (componentRepresentative (secondOrderDefectGraph G) e)).card =
      c.supp.ncard
  exact orderSixtyFour_eight_mul_componentNeighborFinset_card
    G hfree hmin hcover c _

/-- There are at most eight defect components.  Together with the preceding
quotient formula, this reduces the disconnected endpoint to a partition of
eight into positive component weights. -/
theorem orderSixtyFour_defect_component_count_le_eight
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8) :
    Fintype.card (secondOrderDefectGraph G).ConnectedComponent ≤ 8 := by
  classical
  let D := secondOrderDefectGraph G
  change Fintype.card D.ConnectedComponent ≤ 8
  have hsize (c : D.ConnectedComponent) : 8 ≤ c.supp.ncard := by
    apply Nat.le_of_dvd c.nonempty_supp.ncard_pos
    exact orderSixtyFour_eight_dvd_defect_component_order
      G hfree hmin hcover c
  have hsum : (∑ c : D.ConnectedComponent, c.supp.ncard) = 64 := by
    calc
      (∑ c : D.ConnectedComponent, c.supp.ncard) =
          ∑ c : D.ConnectedComponent, Fintype.card c.supp := by
        apply Finset.sum_congr rfl
        intro c _
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq c.supp).symm
      _ = Fintype.card (Σ c : D.ConnectedComponent, c.supp) :=
        Fintype.card_sigma.symm
      _ = Fintype.card (Fin 64) :=
        (Fintype.card_congr (vertexConnectedComponentEquiv D)).symm
      _ = 64 := by simp
  have hbound : 8 * Fintype.card D.ConnectedComponent ≤
      ∑ c : D.ConnectedComponent, c.supp.ncard := by
    calc
      8 * Fintype.card D.ConnectedComponent =
          ∑ _c : D.ConnectedComponent, 8 := by simp [mul_comm]
      _ ≤ ∑ c : D.ConnectedComponent, c.supp.ncard := by
        exact Finset.sum_le_sum fun c _ => hsize c
  rw [hsum] at hbound
  omega

/-- At the extremal component count, every defect component has order eight.
This is the uniform-block branch on which the quadratic trace obstruction
acts. -/
theorem orderSixtyFour_defect_component_order_eq_eight_of_count_eight
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 8)
    (c : (secondOrderDefectGraph G).ConnectedComponent) :
    c.supp.ncard = 8 := by
  classical
  let D := secondOrderDefectGraph G
  have hsize (e : D.ConnectedComponent) : 8 ≤ e.supp.ncard := by
    apply Nat.le_of_dvd e.nonempty_supp.ncard_pos
    exact orderSixtyFour_eight_dvd_defect_component_order
      G hfree hmin hcover e
  have hsum : (∑ e : D.ConnectedComponent, e.supp.ncard) = 64 := by
    calc
      (∑ e : D.ConnectedComponent, e.supp.ncard) =
          ∑ e : D.ConnectedComponent, Fintype.card e.supp := by
        apply Finset.sum_congr rfl
        intro e _
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq e.supp).symm
      _ = Fintype.card (Σ e : D.ConnectedComponent, e.supp) :=
        Fintype.card_sigma.symm
      _ = Fintype.card (Fin 64) :=
        (Fintype.card_congr (vertexConnectedComponentEquiv D)).symm
      _ = 64 := by simp
  have hc : c ∈ (Finset.univ : Finset D.ConnectedComponent) :=
    Finset.mem_univ c
  have hrest : 56 ≤ ∑ e ∈ (Finset.univ.erase c), e.supp.ncard := by
    calc
      56 = ∑ _e ∈ (Finset.univ.erase c : Finset D.ConnectedComponent), 8 := by
        simp [hcount, D]
      _ ≤ ∑ e ∈ (Finset.univ.erase c), e.supp.ncard := by
        exact Finset.sum_le_sum fun e _ => hsize e
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset D.ConnectedComponent)
    (fun e => e.supp.ncard) hc
  have hsplit' :
      (∑ e ∈ (Finset.univ.erase c : Finset D.ConnectedComponent),
          e.supp.ncard) + c.supp.ncard = 64 := by
    calc
      (∑ e ∈ (Finset.univ.erase c : Finset D.ConnectedComponent),
          e.supp.ncard) + c.supp.ncard =
          ∑ e : D.ConnectedComponent, e.supp.ncard := hsplit
      _ = 64 := hsum
  have hplus : 56 + c.supp.ncard ≤ 64 := by
    calc
      56 + c.supp.ncard ≤
          (∑ e ∈ (Finset.univ.erase c : Finset D.ConnectedComponent),
            e.supp.ncard) + c.supp.ncard := Nat.add_le_add_right hrest _
      _ = 64 := hsplit'
  have hupper : c.supp.ncard ≤ 8 := by omega
  exact Nat.le_antisymm hupper (hsize c)

end

end Erdos85
