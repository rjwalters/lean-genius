import Proofs.Erdos85HoffmanRatioBound

/-!
# Equality in the owner-graph Hoffman bound

An order-`q` defect component is not only a maximum coclique in every owner
color.  Its centered indicator is a bottom eigenvector, so the component and
its complement form an equitable two-cell partition of every owner graph.
-/

open SimpleGraph

namespace Erdos85

/-- The centered indicator of an order-`q` set, normalized integrally. -/
def centeredIndicatorInt {V : Type*} [DecidableEq V]
    (q : ℕ) (S : Finset V) : V → ℤ :=
  (q : ℤ) • finsetIndicatorInt S - fun _ => 1

/-- Equality in the sharp owner-color Hoffman bound gives the full bottom
eigenvector equation.  This graph-facing form uses the existing exact
sum-of-squares factorization of the shifted owner matrix. -/
theorem binarySquare_regular_sizeQ_component_centeredIndicator_mulVec_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (hc : c.supp.ncard = q * m_c) (he : e.supp.ncard = q) :
    (((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ +
      (m_c : ℤ) • 1).mulVec
        (centeredIndicatorInt q e.supp.toFinite.toFinset)) = 0 := by
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  let S := e.supp.toFinite.toFinset
  let chi := finsetIndicatorInt S
  let one : V → ℤ := fun _ => 1
  let v := centeredIndicatorInt q S
  have hScard : S.card = q := by
    exact (Set.ncard_eq_toFinset_card e.supp e.supp.toFinite).symm.trans he
  have hind : O.IsIndepSet (S : Set V) := by
    rw [SimpleGraph.isIndepSet_iff]
    intro x hx y hy hxy hAdj
    have hxcomp : (secondOrderDefectGraph G).connectedComponentMk x = e :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff e x).mp (by simpa [S] using hx)
    have hycomp : (secondOrderDefectGraph G).connectedComponentMk y = e :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff e y).mp (by simpa [S] using hy)
    exact binarySquare_regular_sizeQ_component_not_componentOwnerGraph_adj
      G hfree hq hreg hcard e c hc he hxcomp hycomp hAdj
  have hOreg : ∀ x, O.degree x = m_c * (q - 1) :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard c hc
  have hOone : (O.adjMatrix ℤ).mulVec one =
      (m_c * (q - 1) : ℕ) • one := by
    funext x
    change (O.adjMatrix ℤ).mulVec (Function.const V 1) x =
      (((m_c * (q - 1) : ℕ) : ℤ) • one) x
    rw [SimpleGraph.adjMatrix_mulVec_const_apply, mul_one, hOreg x]
    simp [one]
  have hchi : chi ⬝ᵥ (O.adjMatrix ℤ).mulVec chi = 0 :=
    adjMatrix_indicatorInt_quadratic_eq_zero O S hind
  have hsymm : Matrix.conjTranspose (O.adjMatrix ℤ) = O.adjMatrix ℤ := by
    ext x y
    by_cases hxy : O.Adj x y
    · simp [Matrix.conjTranspose_apply, SimpleGraph.adjMatrix_apply, hxy, hxy.symm]
    · have hyx : ¬ O.Adj y x := fun hyx => hxy hyx.symm
      simp [Matrix.conjTranspose_apply, SimpleGraph.adjMatrix_apply, hxy, hyx]
  have hchiOne : chi ⬝ᵥ (O.adjMatrix ℤ).mulVec one =
      (m_c * (q - 1) : ℕ) * (q : ℤ) := by
    rw [hOone]
    rw [dotProduct_smul, dotProduct_finsetIndicatorInt_one, hScard]
    simp [chi, one, S, mul_comm]
  have honeChi : one ⬝ᵥ (O.adjMatrix ℤ).mulVec chi =
      (m_c * (q - 1) : ℕ) * (q : ℤ) := by
    calc
      one ⬝ᵥ (O.adjMatrix ℤ).mulVec chi =
          star one ⬝ᵥ (O.adjMatrix ℤ).mulVec chi := by simp [one]
      _ = star ((O.adjMatrix ℤ).mulVec one) ⬝ᵥ chi := by
        rw [Matrix.star_mulVec, hsymm, Matrix.dotProduct_mulVec]
      _ = (m_c * (q - 1) : ℕ) * (q : ℤ) := by
        rw [hOone]
        change (((m_c * (q - 1) : ℕ) : ℤ) • one) ⬝ᵥ chi = _
        rw [smul_dotProduct, dotProduct_one_finsetIndicatorInt, hScard]
        simp [chi, one, S, mul_comm]
  have honeOne : one ⬝ᵥ (O.adjMatrix ℤ).mulVec one =
      (m_c * (q - 1) : ℕ) * ((q * q : ℕ) : ℤ) := by
    rw [hOone]
    simp [dotProduct, one, hcard, mul_comm]
  have hv : v = (q : ℤ) • chi - one := by
    rfl
  have hchiChi : chi ⬝ᵥ chi = (q : ℤ) := by
    simpa [chi, hScard] using dotProduct_finsetIndicatorInt_self S
  have hchiOne' : chi ⬝ᵥ one = (q : ℤ) := by
    simpa [chi, one, hScard] using dotProduct_finsetIndicatorInt_one S
  have honeChi' : one ⬝ᵥ chi = (q : ℤ) := by
    simpa [chi, one, hScard] using dotProduct_one_finsetIndicatorInt S
  have honeOne' : one ⬝ᵥ one = ((q * q : ℕ) : ℤ) := by
    simpa [one, hcard] using (dotProduct_one_one_int (V := V))
  have hnorm : v ⬝ᵥ v = ((q * q * (q - 1) : ℕ) : ℤ) := by
    rw [hv, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct]
    simp only [dotProduct_smul, smul_dotProduct, sub_dotProduct,
      hchiChi, hchiOne', honeChi', honeOne']
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ q)]
    ring
  have hOquad : v ⬝ᵥ (O.adjMatrix ℤ).mulVec v =
      -((m_c * (q - 1) * q * q : ℕ) : ℤ) := by
    rw [hv]
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, dotProduct_sub,
      sub_dotProduct, dotProduct_smul, smul_dotProduct]
    rw [hchi, hchiOne, honeChi, honeOne]
    push_cast
    ring
  have hquad : star v ⬝ᵥ
      ((O.adjMatrix ℤ + (m_c : ℤ) • 1).mulVec v) = 0 := by
    have hvstar : star v = v := by funext x; simp [v, centeredIndicatorInt]
    rw [hvstar, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_add, dotProduct_smul, hOquad, hnorm]
    push_cast
    ring
  have hzero :=
    (binarySquare_regular_componentOwnerGraph_shifted_quadratic_eq_zero_iff
      G hfree hq hreg hcard c hc v).mp hquad
  rw [binarySquare_regular_componentOwnerGraph_adjMatrix_eq
    G hfree hq hreg hcard c hc, sub_add_cancel]
  change (G.adjMatrix ℤ *
    defectComponentDiagonalMatrix (K := ℤ) (secondOrderDefectGraph G) c *
    G.adjMatrix ℤ).mulVec v = 0
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  funext x
  rw [Matrix.mulVec, dotProduct]
  apply Finset.sum_eq_zero
  intro y _hy
  have hP :
      (defectComponentDiagonalMatrix (K := ℤ) (secondOrderDefectGraph G) c).mulVec
          ((G.adjMatrix ℤ).mulVec v) y = 0 := by
    calc
      _ = if (secondOrderDefectGraph G).connectedComponentMk y = c then
          (G.adjMatrix ℤ).mulVec v y else 0 := by
            simp [defectComponentDiagonalMatrix, Matrix.mulVec]
      _ = 0 := by
        by_cases hyc : (secondOrderDefectGraph G).connectedComponentMk y = c
        · simp [hyc, hzero y hyc]
        · simp [hyc]
  simp [hP]

/-- **Equitable Hoffman partition.**  In the owner graph of `c`, an order-`q`
defect component `e` has owner-degree zero from its own vertices and exactly
`m_c` from every vertex outside it.  The matrix formula is the indicator-vector
form of that assertion. -/
theorem binarySquare_regular_sizeQ_component_ownerIndicator_mulVec
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (e c : (secondOrderDefectGraph G).ConnectedComponent) {m_c : ℕ}
    (hc : c.supp.ncard = q * m_c) (he : e.supp.ncard = q) (x : V) :
    ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ).mulVec
        (finsetIndicatorInt e.supp.toFinite.toFinset) x =
      if x ∈ e.supp then 0 else (m_c : ℤ) := by
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  let S := e.supp.toFinite.toFinset
  let chi := finsetIndicatorInt S
  let one : V → ℤ := fun _ => 1
  have hker :=
    binarySquare_regular_sizeQ_component_centeredIndicator_mulVec_eq_zero
      G hfree hq hreg hcard e c hc he
  have hOreg : O.degree x = m_c * (q - 1) :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard c hc x
  have hOone : (O.adjMatrix ℤ).mulVec one x =
      ((m_c * (q - 1) : ℕ) : ℤ) := by
    change (O.adjMatrix ℤ).mulVec (Function.const V 1) x = _
    rw [SimpleGraph.adjMatrix_mulVec_const_apply, mul_one, hOreg]
  have hxker := congrFun hker x
  change ((O.adjMatrix ℤ + (m_c : ℤ) • 1).mulVec
      ((q : ℤ) • chi - one)) x = 0 at hxker
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul, one, mul_one] at hxker
  rw [hOone] at hxker
  by_cases hx : x ∈ e.supp
  · have hxS : x ∈ S := by simpa [S] using hx
    have hchi : chi x = 1 := by simp [chi, finsetIndicatorInt, hxS]
    simp only [hchi] at hxker
    rw [if_pos hx]
    change (O.adjMatrix ℤ).mulVec chi x = 0
    have hqZ : (q : ℤ) ≠ 0 := by omega
    have heq : (q : ℤ) * ((O.adjMatrix ℤ).mulVec chi x) = 0 := by
      simp only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one] at hxker
      nlinarith
    exact (mul_eq_zero.mp heq).resolve_left hqZ
  · have hxS : x ∉ S := by simpa [S] using hx
    have hchi : chi x = 0 := by simp [chi, finsetIndicatorInt, hxS]
    simp only [hchi] at hxker
    rw [if_neg hx]
    change (O.adjMatrix ℤ).mulVec chi x = (m_c : ℤ)
    have hqZ : (q : ℤ) ≠ 0 := by omega
    apply (mul_left_cancel₀ hqZ)
    simp only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one] at hxker
    nlinarith

end Erdos85
