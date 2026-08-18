import Proofs.Erdos85BinarySquareRegularParity

/-!
# A sharp Hoffman ratio bound for the owner graphs

This file packages the elementary shifted-positive-semidefinite proof of
Hoffman's independent-set bound and applies it to the owner-color graphs in a
regular square-order core.
-/

open SimpleGraph

namespace Erdos85

/-- Integral indicator vector of a finite vertex set. -/
def finsetIndicatorInt {V : Type*} [DecidableEq V] (S : Finset V) : V → ℤ :=
  fun x => if x ∈ S then 1 else 0

@[simp] theorem sum_finsetIndicatorInt
    {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) :
    ∑ x, finsetIndicatorInt S x = (S.card : ℤ) := by
  simp [finsetIndicatorInt]

@[simp] theorem dotProduct_finsetIndicatorInt_self
    {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) :
    finsetIndicatorInt S ⬝ᵥ finsetIndicatorInt S = (S.card : ℤ) := by
  simp [dotProduct, finsetIndicatorInt]

@[simp] theorem dotProduct_finsetIndicatorInt_one
    {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) :
    finsetIndicatorInt S ⬝ᵥ (fun _ => (1 : ℤ)) = (S.card : ℤ) := by
  simp [dotProduct, finsetIndicatorInt]

@[simp] theorem dotProduct_one_finsetIndicatorInt
    {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) :
    (fun _ => (1 : ℤ)) ⬝ᵥ finsetIndicatorInt S = (S.card : ℤ) := by
  simp [dotProduct, finsetIndicatorInt]

@[simp] theorem dotProduct_one_one_int
    {V : Type*} [Fintype V] :
    (fun _ : V => (1 : ℤ)) ⬝ᵥ (fun _ => (1 : ℤ)) =
      (Fintype.card V : ℤ) := by
  simp [dotProduct]

/-- The adjacency quadratic form of an independent-set indicator is zero. -/
theorem adjMatrix_indicatorInt_quadratic_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (S : Finset V)
    (hind : H.IsIndepSet (S : Set V)) :
    finsetIndicatorInt S ⬝ᵥ
      (H.adjMatrix ℤ).mulVec (finsetIndicatorInt S) = 0 := by
  rw [dotProduct]
  apply Finset.sum_eq_zero
  intro x _hx
  by_cases hxS : x ∈ S
  · have hrow : (H.adjMatrix ℤ).mulVec (finsetIndicatorInt S) x = 0 := by
      rw [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro y _hy
      by_cases hxy : H.Adj x y
      · have hyS : y ∉ S := by
          intro hyS
          rw [SimpleGraph.isIndepSet_iff] at hind
          exact hind hxS hyS hxy.ne hxy
        simp [SimpleGraph.adjMatrix_apply, hxy, finsetIndicatorInt, hyS]
      · simp [SimpleGraph.adjMatrix_apply, hxy]
    simp [finsetIndicatorInt, hxS, hrow]
  · simp [finsetIndicatorInt, hxS]

/-- Integer form of Hoffman's ratio bound.  If a `k`-regular graph has
`Adj + tau I` positive semidefinite, every independent set `S` satisfies
`(k+tau)|S| <= tau|V|`. -/
theorem hoffman_card_bound_of_shifted_adjMatrix_posSemidef
    {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (k tau : ℕ) (hreg : ∀ x, H.degree x = k)
    (hPSD : (H.adjMatrix ℤ + (tau : ℤ) • 1).PosSemidef)
    (S : Finset V) (hind : H.IsIndepSet (S : Set V)) :
    (k + tau) * S.card ≤ tau * Fintype.card V := by
  by_cases hs0 : S.card = 0
  · simp [hs0]
  have hSne : S.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hs0)
  have hn0 : 0 < Fintype.card V := by
    exact Fintype.card_pos_iff.mpr ⟨hSne.choose⟩
  let n : ℤ := Fintype.card V
  let s : ℤ := S.card
  let chi := finsetIndicatorInt S
  let one : V → ℤ := fun _ => 1
  let v : V → ℤ := n • chi - s • one
  have hAone : (H.adjMatrix ℤ).mulVec one = (k : ℤ) • one := by
    funext x
    simp only [one, Pi.smul_apply, smul_eq_mul, mul_one]
    change (H.adjMatrix ℤ).mulVec (Function.const V 1) x = (k : ℤ)
    rw [SimpleGraph.adjMatrix_mulVec_const_apply, mul_one, hreg x]
  have hchi : chi ⬝ᵥ (H.adjMatrix ℤ).mulVec chi = 0 := by
    exact adjMatrix_indicatorInt_quadratic_eq_zero H S hind
  have hA : Matrix.conjTranspose (H.adjMatrix ℤ) = H.adjMatrix ℤ := by
    ext x y
    by_cases hxy : H.Adj x y
    · simp [Matrix.conjTranspose_apply, SimpleGraph.adjMatrix_apply, hxy, hxy.symm]
    · have hyx : ¬ H.Adj y x := fun hyx => hxy hyx.symm
      simp [Matrix.conjTranspose_apply, SimpleGraph.adjMatrix_apply, hxy, hyx]
  have hchiAone : chi ⬝ᵥ (H.adjMatrix ℤ).mulVec one = (k : ℤ) * s := by
    rw [hAone]
    simp [dotProduct, chi, one, s, finsetIndicatorInt,
      mul_comm]
  have honeAchi : one ⬝ᵥ (H.adjMatrix ℤ).mulVec chi = (k : ℤ) * s := by
    calc
      one ⬝ᵥ (H.adjMatrix ℤ).mulVec chi =
          star one ⬝ᵥ (H.adjMatrix ℤ).mulVec chi := by simp [one]
      _ = star ((H.adjMatrix ℤ).mulVec one) ⬝ᵥ chi := by
        rw [Matrix.star_mulVec, hA, Matrix.dotProduct_mulVec]
      _ = (k : ℤ) * s := by
        rw [hAone]
        simp [dotProduct, chi, one, s, finsetIndicatorInt,
          mul_comm]
  have honeAone : one ⬝ᵥ (H.adjMatrix ℤ).mulVec one =
      (k : ℤ) * n := by
    rw [hAone]
    simp [dotProduct, one, n, mul_comm]
  have hquad :
      v ⬝ᵥ (H.adjMatrix ℤ).mulVec v = -(n * s * s * (k : ℤ)) := by
    simp only [v, Matrix.mulVec_sub, Matrix.mulVec_smul,
      dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct]
    rw [hchi, hchiAone, honeAchi, honeAone]
    ring
  have hnorm : v ⬝ᵥ v = n * s * (n - s) := by
    simp only [v, dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct]
    rw [dotProduct_finsetIndicatorInt_self,
      dotProduct_finsetIndicatorInt_one, dotProduct_one_finsetIndicatorInt,
      dotProduct_one_one_int]
    change n * (n * s - s * s) - s * (n * s - s * n) = _
    ring
  have hnonneg := hPSD.dotProduct_mulVec_nonneg v
  have hstar : star v = v := by
    funext x
    simp
  rw [hstar, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_add, dotProduct_smul, hquad, hnorm] at hnonneg
  have hnZ : 0 < n := by
    dsimp [n]
    exact_mod_cast hn0
  have hsZ : 0 < s := by
    dsimp [s]
    exact_mod_cast Nat.pos_of_ne_zero hs0
  have hineqZ : ((k + tau : ℕ) : ℤ) * s ≤ (tau : ℤ) * n := by
    have hfactor : 0 ≤ n * s *
        ((tau : ℤ) * n - ((k + tau : ℕ) : ℤ) * s) := by
      calc
        0 ≤ -(n * s * s * (k : ℤ)) +
            (tau : ℤ) * (n * s * (n - s)) := hnonneg
        _ = n * s * ((tau : ℤ) * n - ((k + tau : ℕ) : ℤ) * s) := by
          push_cast
          ring
    have hfactor' : 0 ≤
        ((tau : ℤ) * n - ((k + tau : ℕ) : ℤ) * s) * (n * s) := by
      simpa [mul_comm] using hfactor
    have hbase : 0 ≤ (tau : ℤ) * n - ((k + tau : ℕ) : ℤ) * s :=
      nonneg_of_mul_nonneg_left hfactor' (mul_pos hnZ hsZ)
    linarith
  dsimp [n, s] at hineqZ
  exact_mod_cast hineqZ

/-- **Sharp owner-color Hoffman bound.** Every independent set in a nonzero
owner color has at most `q` vertices. -/
theorem binarySquare_regular_componentOwnerGraph_indepSet_card_le
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
    (hc : c.supp.ncard = q * m_c) (hmc : 0 < m_c)
    (S : Finset V)
    (hind : (componentOwnerGraph G (secondOrderDefectGraph G) c).IsIndepSet
      (S : Set V)) :
    S.card ≤ q := by
  let O := componentOwnerGraph G (secondOrderDefectGraph G) c
  have hOreg : ∀ x, O.degree x = m_c * (q - 1) :=
    binarySquare_regular_componentOwnerGraph_degree
      G hfree hq hreg hcard c hc
  have hPSD : (O.adjMatrix ℤ + (m_c : ℤ) • 1).PosSemidef :=
    binarySquare_regular_componentOwnerGraph_adjMatrix_add_posSemidef
      G hfree hq hreg hcard c hc
  have hb := hoffman_card_bound_of_shifted_adjMatrix_posSemidef
    O (m_c * (q - 1)) m_c hOreg hPSD S hind
  rw [hcard] at hb
  have hsum : m_c * (q - 1) + m_c = m_c * q := by
    calc
      m_c * (q - 1) + m_c = m_c * (q - 1) + m_c * 1 := by rw [Nat.mul_one]
      _ = m_c * ((q - 1) + 1) := by rw [Nat.mul_add]
      _ = m_c * q := by rw [Nat.sub_add_cancel (by omega : 1 ≤ q)]
  rw [hsum] at hb
  have hb' : m_c * (q * S.card) ≤ m_c * (q * q) := by
    simpa [Nat.mul_assoc] using hb
  have hqbound : q * S.card ≤ q * q :=
    Nat.le_of_mul_le_mul_left hb' hmc
  exact Nat.le_of_mul_le_mul_left hqbound (by omega)

/-- A minimum defect component is a maximum independent set in every nonzero
owner color, attaining the sharp Hoffman bound simultaneously. -/
theorem binarySquare_regular_sizeQ_component_isMaximumIndepSet_componentOwnerGraph
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
    (hc : c.supp.ncard = q * m_c) (hmc : 0 < m_c)
    (he : e.supp.ncard = q) :
    (componentOwnerGraph G (secondOrderDefectGraph G) c).IsMaximumIndepSet
      e.supp.toFinite.toFinset := by
  constructor
  · rw [SimpleGraph.isIndepSet_iff]
    intro x hx y hy hxy hAdj
    have hxcomp : (secondOrderDefectGraph G).connectedComponentMk x = e :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff e x).mp (by simpa using hx)
    have hycomp : (secondOrderDefectGraph G).connectedComponentMk y = e :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff e y).mp (by simpa using hy)
    exact binarySquare_regular_sizeQ_component_not_componentOwnerGraph_adj
      G hfree hq hreg hcard e c hc he hxcomp hycomp hAdj
  · intro T hT
    have hle := binarySquare_regular_componentOwnerGraph_indepSet_card_le
      G hfree hq hreg hcard c hc hmc T hT
    have hecard : e.supp.toFinite.toFinset.card = q :=
      (Set.ncard_eq_toFinset_card e.supp e.supp.toFinite).symm.trans he
    rw [hecard]
    exact hle

end Erdos85
