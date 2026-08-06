import Proofs.Erdos85PositiveExcessDeterminant
import Proofs.Erdos85MixedSectorMassQuotient

/-!
# Weighted quotient trace at positive excess

The connected components of the `(e+2)`-regular combined defect graph form
an equitable partition for the adjacency operator.  Its weighted quotient
satisfies

`Q² = (d-e-3)I + 1 rᵀ`.

Consequently, in the nonsquare branch its trace is exactly `d`, just as at
the zero-excess boundary.  No classification of defect components is used.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem adjMatrix_comm_secondOrderDefect_of_regular_real
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) :
    G.adjMatrix ℝ * (secondOrderDefectGraph G).adjMatrix ℝ =
      (secondOrderDefectGraph G).adjMatrix ℝ * G.adjMatrix ℝ := by
  have hz := adjMatrix_comm_secondOrderDefect_of_regular G hfree hreg
  have h := congrArg (fun M ↦ M.map (Int.castRingHom ℝ)) hz
  simpa only [Matrix.map_mul, adjMatrix_map_intCast] using h

theorem adjMatrix_sq_eq_sub_secondOrderDefect_of_regular_real
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ}
    (hreg : ∀ x, G.degree x = d) :
    G.adjMatrix ℝ * G.adjMatrix ℝ =
      (d - 1 : ℝ) • (1 : Matrix V V ℝ) + realOnesMatrix V -
        (secondOrderDefectGraph G).adjMatrix ℝ := by
  have hz := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular G hfree hreg
  have h := congrArg (fun M ↦ M.map (Int.castRingHom ℝ)) hz
  simp only [Matrix.map_mul, adjMatrix_map_intCast] at h
  rw [h]
  ext x y
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
    FriendshipTheoremOQ01.onesMatrix, realOnesMatrix,
    SimpleGraph.adjMatrix_apply, smul_eq_mul]
  split_ifs <;> simp only [eq_intCast] <;> push_cast <;> ring

/-- Positive-excess quotient square equation over the reals. -/
theorem positiveExcess_componentQuotientMatrixReal_sq_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (c f : (secondOrderDefectGraph G).ConnectedComponent) :
    (componentQuotientMatrixReal G (secondOrderDefectGraph G) *
        componentQuotientMatrixReal G (secondOrderDefectGraph G)) c f =
      ((d - e - 3 : ℕ) : ℝ) * (if c = f then 1 else 0) +
        (f.supp.ncard : ℝ) := by
  let D := secondOrderDefectGraph G
  let S := componentMembershipMatrix D
  let Q := componentQuotientMatrixReal G D
  let R : Matrix V D.ConnectedComponent ℝ :=
    fun _ a => (a.supp.ncard : ℝ)
  have hDreg : ∀ x, D.degree x = e + 2 :=
    secondOrderDefectGraph_degree_eq_excess_add_two G hfree hreg hcard
  have hcomm := adjMatrix_comm_secondOrderDefect_of_regular_real G hfree hreg
  have hAS : G.adjMatrix ℝ * S = S * Q :=
    adjMatrix_mul_componentMembershipMatrix G D (e + 2) hDreg hcomm
  have hDS : D.adjMatrix ℝ * S = (e + 2 : ℝ) • S :=
    by
      simpa only [S, Nat.cast_add, Nat.cast_ofNat] using
        (adjMatrix_mul_componentMembershipMatrix_self D (e + 2) hDreg)
  have hJS : realOnesMatrix V * S = R :=
    onesMatrix_mul_componentMembershipMatrix D
  have hsq := adjMatrix_sq_eq_sub_secondOrderDefect_of_regular_real G hfree hreg
  have htransport :
      S * (Q * Q) =
        ((d - 1 : ℝ) • (1 : Matrix V V ℝ) + realOnesMatrix V -
          D.adjMatrix ℝ) * S := by
    calc
      S * (Q * Q) = (S * Q) * Q := (Matrix.mul_assoc S Q Q).symm
      _ = (G.adjMatrix ℝ * S) * Q := by rw [hAS]
      _ = G.adjMatrix ℝ * (S * Q) := Matrix.mul_assoc _ _ _
      _ = G.adjMatrix ℝ * (G.adjMatrix ℝ * S) := by rw [hAS]
      _ = (G.adjMatrix ℝ * G.adjMatrix ℝ) * S :=
        (Matrix.mul_assoc _ _ _).symm
      _ = ((d - 1 : ℝ) • (1 : Matrix V V ℝ) + realOnesMatrix V -
          D.adjMatrix ℝ) * S := by rw [hsq]
  have htransport' : S * (Q * Q) =
      (d - 1 : ℝ) • S + R - (e + 2 : ℝ) • S := by
    calc
      S * (Q * Q) =
          ((d - 1 : ℝ) • (1 : Matrix V V ℝ) + realOnesMatrix V -
            D.adjMatrix ℝ) * S := htransport
      _ = (d - 1 : ℝ) • S + R - (e + 2 : ℝ) • S := by
        rw [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul,
          hJS, hDS]
  have hentry := congrFun (congrFun htransport'
    (componentRepresentative D c)) f
  have hrep : D.connectedComponentMk (componentRepresentative D c) = c :=
    (SimpleGraph.ConnectedComponent.mem_supp_iff c
      (componentRepresentative D c)).mp (componentRepresentative_mem D c)
  simp [Matrix.mul_apply, S, Q, R, componentMembershipMatrix, hrep] at hentry ⊢
  have hcast : ((d - e - 3 : ℕ) : ℝ) = (d : ℝ) - e - 3 := by
    rw [Nat.cast_sub (by omega : 3 ≤ d - e),
      Nat.cast_sub (by omega : e ≤ d)]
    norm_num
  rw [hcast]
  by_cases hcf : c = f
  · simp [hcf] at hentry ⊢
    linarith
  · simp [hcf] at hentry ⊢
    linarith

/-- Integral positive-excess quotient square equation. -/
theorem positiveExcess_componentQuotientMatrix_sq_apply
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (c f : (secondOrderDefectGraph G).ConnectedComponent) :
    (componentQuotientMatrix G (secondOrderDefectGraph G) *
        componentQuotientMatrix G (secondOrderDefectGraph G)) c f =
      (d - e - 3) * (if c = f then 1 else 0) + f.supp.ncard := by
  have hr := positiveExcess_componentQuotientMatrixReal_sq_apply
    G hfree hd he hreg hcard c f
  simp only [Matrix.mul_apply, componentQuotientMatrixReal] at hr ⊢
  exact_mod_cast hr

/-- **Positive-excess weighted trace identity.**  If the transverse scalar
`d-e-3` is nonsquare, the component quotient trace is exactly `d`. -/
theorem positiveExcess_componentQuotient_trace_eq_degree_of_nonsquare
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {d e : ℕ} (hd : 4 ≤ d)
    (he : e ≤ d - 4) (hreg : ∀ x, G.degree x = d)
    (hcard : Fintype.card V = d * (d - 1) + 3 + e)
    (hnonsquare : ¬ IsSquare (d - e - 3)) :
    ∑ c, componentQuotientMatrix G (secondOrderDefectGraph G) c c = d := by
  let D := secondOrderDefectGraph G
  let I := D.ConnectedComponent
  let Q := componentQuotientMatrixRat G D
  let r : I → ℚ := fun c ↦ c.supp.ncard
  letI : Nonempty V := Fintype.card_pos_iff.mp (by rw [hcard]; omega)
  letI : Nonempty I :=
    ⟨D.connectedComponentMk (Classical.choice (inferInstance : Nonempty V))⟩
  have hparts : (∑ c : I, c.supp.ncard) = Fintype.card V := by
    calc
      (∑ c : I, c.supp.ncard) =
          ∑ c : I, Fintype.card c.supp := by
        apply Finset.sum_congr rfl
        intro c _
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq c.supp).symm
      _ = Fintype.card (Σ c : I, c.supp) := Fintype.card_sigma.symm
      _ = Fintype.card V :=
        (Fintype.card_congr (vertexConnectedComponentEquiv D)).symm
  have hR : (∑ c : I, r c) ≠ 0 := by
    have hpartsQ : (∑ c : I, r c) = (Fintype.card V : ℚ) := by
      simp only [r]
      exact_mod_cast hparts
    rw [hpartsQ]
    exact_mod_cast (Fintype.card_ne_zero : Fintype.card V ≠ 0)
  have hrow : ∀ c : I, ∑ f, Q c f = (d : ℚ) := by
    intro c
    simp only [Q, D, componentQuotientMatrixRat]
    have hr := sum_componentQuotientMatrix_row G D c
    rw [hreg] at hr
    exact_mod_cast hr
  have hDreg : ∀ x, D.degree x = e + 2 :=
    secondOrderDefectGraph_degree_eq_excess_add_two G hfree hreg hcard
  have hcomm := adjMatrix_comm_secondOrderDefect_of_regular_real G hfree hreg
  have hleft : ∀ f : I, ∑ c, r c * Q c f = (d : ℚ) * r f := by
    intro f
    calc
      ∑ c, r c * Q c f = ∑ c, r f * Q f c := by
        apply Finset.sum_congr rfl
        intro c _
        simp only [r, Q, D, componentQuotientMatrixRat]
        exact_mod_cast (componentQuotientMatrix_balance G D (e + 2)
          hDreg hcomm c f)
      _ = r f * ∑ c, Q f c := by rw [Finset.mul_sum]
      _ = (d : ℚ) * r f := by rw [hrow]; ring
  have hsq : Q * Q = ((d - e - 3 : ℕ) : ℚ) •
      (1 : Matrix I I ℚ) + Matrix.of (fun _ f ↦ r f) := by
    ext c f
    have hs := positiveExcess_componentQuotientMatrix_sq_apply
      G hfree hd he hreg hcard c f
    simp only [Matrix.mul_apply, Q, componentQuotientMatrixRat,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.of_apply, r, smul_eq_mul] at hs ⊢
    exact_mod_cast hs
  have htrace := Matrix.trace_eq_degree_of_sq_weightedRankOne_of_nonsquare
    Q r (d : ℚ) (d - e - 3) hR hrow hleft hsq hnonsquare
  rw [Matrix.trace] at htrace
  have htraceQ :
      (∑ c : I, (componentQuotientMatrix G D c c : ℚ)) = d := by
    simpa only [Q, Matrix.diag, componentQuotientMatrixRat] using htrace
  exact_mod_cast htraceQ

end

end Erdos85
