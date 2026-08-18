import Proofs.Erdos85BinarySquareRealOwnerCommonBottomExact

/-! # Two owner-bottom sectors fill the zero-sum hyperplane

Every shifted-owner bottom vector has coordinate sum zero.  Combining this
with the exact two-owner span dimension identifies that span with the full
zero-sum hyperplane, giving a concrete decomposition target for centered
routing vectors.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Coordinate summation as a real linear functional. -/
def realCoordinateSumLinearMap {V : Type*} [Fintype V] :
    (V → ℝ) →ₗ[ℝ] ℝ where
  toFun v := ∑ x, v x
  map_add' u v := by simp [Finset.sum_add_distrib]
  map_smul' r v := by simp [Finset.mul_sum]

/-- The real zero-coordinate-sum hyperplane. -/
def realZeroSumSubmodule {V : Type*} [Fintype V] : Submodule ℝ (V → ℝ) :=
  LinearMap.ker realCoordinateSumLinearMap

/-- Exact dimension of the zero-sum hyperplane. -/
theorem finrank_realZeroSumSubmodule
    {V : Type*} [Fintype V] [Nonempty V] :
    Module.finrank ℝ (realZeroSumSubmodule (V := V)) = Fintype.card V - 1 := by
  have hf : (realCoordinateSumLinearMap (V := V)) ≠ 0 := by
    intro hz
    have h := LinearMap.congr_fun hz (fun _ => (1 : ℝ))
    simp [realCoordinateSumLinearMap] at h
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hf
  have htarget : Module.finrank ℝ (realZeroSumSubmodule (V := V)) + 1 =
      Fintype.card V := by
    calc
      _ = Module.finrank ℝ (V → ℝ) := hdim
      _ = Fintype.card V := Module.finrank_fintype_fun_eq_card ℝ
  have hpos : 1 ≤ Fintype.card V := Fintype.card_pos_iff.mpr inferInstance
  omega

private theorem sum_adjMatrix_mulVec_of_regular
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ)
    (hreg : ∀ x, H.degree x = k) (v : V → ℝ) :
    ∑ x, (H.adjMatrix ℝ).mulVec v x = (k : ℝ) * ∑ x, v x := by
  let ones : V → ℝ := fun _ => 1
  have hOne : (H.adjMatrix ℝ).mulVec ones = fun _ => (k : ℝ) := by
    funext x
    change (H.adjMatrix ℝ).mulVec (Function.const V 1) x = (k : ℝ)
    rw [SimpleGraph.adjMatrix_mulVec_const_apply, hreg x]
    simp
  have hdot : ones ⬝ᵥ ((H.adjMatrix ℝ).mulVec v) =
      ((H.adjMatrix ℝ).mulVec ones) ⬝ᵥ v := by
    rw [Matrix.dotProduct_mulVec]
    have hsymm : (H.adjMatrix ℝ).transpose = H.adjMatrix ℝ :=
      H.isSymm_adjMatrix.eq
    rw [← hsymm, Matrix.vecMul_transpose]
    rw [hsymm]
  calc
    ∑ x, (H.adjMatrix ℝ).mulVec v x =
        ones ⬝ᵥ ((H.adjMatrix ℝ).mulVec v) := by
      simp [dotProduct, ones]
    _ = ((H.adjMatrix ℝ).mulVec ones) ⬝ᵥ v := hdot
    _ = (k : ℝ) * ∑ x, v x := by
      rw [hOne]
      simp [dotProduct, Finset.mul_sum]

/-- Every individual real owner-bottom vector has coordinate sum zero. -/
theorem binarySquare_regular_realComponentOwnerBottomSubmodule_le_zeroSum
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
    realComponentOwnerBottomSubmodule G c m_c ≤
      realZeroSumSubmodule := by
  intro v hv
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  have hOreg : ∀ x, O.degree x = m_c * (q - 1) :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard c hc
  have hMv : (O.adjMatrix ℝ).mulVec v + (m_c : ℝ) • v = 0 := by
    simpa [realComponentOwnerBottomSubmodule, LinearMap.mem_ker,
      Matrix.mulVecLin_apply, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec] using hv
  have hs := congrArg (fun w : V → ℝ => ∑ x, w x) hMv
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
    Finset.sum_add_distrib, Finset.sum_const_zero] at hs
  rw [sum_adjMatrix_mulVec_of_regular O (m_c * (q - 1)) hOreg] at hs
  have hmpos : 0 < m_c := by
    have hcpos : 0 < c.supp.ncard := c.nonempty_supp.ncard_pos
    rw [hc] at hcpos
    by_contra hm
    have hm0 : m_c = 0 := Nat.eq_zero_of_not_pos hm
    rw [hm0, Nat.mul_zero] at hcpos
    omega
  have hcoef : (m_c * (q - 1) : ℕ) + m_c = q * m_c := by
    calc
      m_c * (q - 1) + m_c = m_c * (q - 1) + m_c * 1 := by
        rw [Nat.mul_one]
      _ = m_c * ((q - 1) + 1) := by rw [Nat.mul_add]
      _ = m_c * q := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
      _ = q * m_c := by rw [Nat.mul_comm]
  have hsum : ∑ x, (v : V → ℝ) x = 0 := by
    simp_rw [smul_eq_mul] at hs
    rw [← Finset.mul_sum, ← add_mul] at hs
    have hcoefR : ((m_c * (q - 1) : ℕ) : ℝ) + (m_c : ℝ) =
        ((q * m_c : ℕ) : ℝ) := by exact_mod_cast hcoef
    rw [hcoefR] at hs
    have hqm : (((q * m_c : ℕ) : ℝ)) ≠ 0 := by positivity
    exact (mul_eq_zero.mp hs).resolve_left hqm
  exact hsum

/-- **Concrete two-owner span.**  With exactly two defect components, the
join of their owner-bottom spaces is the entire zero-sum hyperplane. -/
theorem binarySquare_regular_twoOwner_bottom_sup_eq_zeroSum
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
    realComponentOwnerBottomSubmodule G a (m a) ⊔
        realComponentOwnerBottomSubmodule G b (m b) =
      realZeroSumSubmodule := by
  letI : Nonempty V := Fintype.card_pos_iff.mp (by rw [hcard]; positivity)
  have hle : realComponentOwnerBottomSubmodule G a (m a) ⊔
      realComponentOwnerBottomSubmodule G b (m b) ≤ realZeroSumSubmodule := by
    exact sup_le
      (binarySquare_regular_realComponentOwnerBottomSubmodule_le_zeroSum
        G hfree hq hreg hcard a (hm a))
      (binarySquare_regular_realComponentOwnerBottomSubmodule_le_zeroSum
        G hfree hq hreg hcard b (hm b))
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [(binarySquare_regular_twoOwner_bottom_inter_inf_and_sup_finrank
    G hfree hq hreg hcard m hm hsum hcount a b hab).2,
    finrank_realZeroSumSubmodule, hcard]

end

end Erdos85

#print axioms Erdos85.binarySquare_regular_twoOwner_bottom_sup_eq_zeroSum
