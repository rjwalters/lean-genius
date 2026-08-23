import Proofs.Erdos85OddSquareOrderNineNearRegularCutArithmetic

/-! # Arithmetic classification of q=9 B3-articulation shores

If deleting the unique bin-three owner disconnects the ordinary defect graph,
each resulting component contains `e` exceptional bin-zero vertices, `5k`
regular bin-zero vertices, and `3k` bin-one vertices.  Its order is `e+8k`
and its defect boundary is `e`.  This module kernel-enumerates the bounded
cut inequalities and records the much smaller list of possible `(e,k)` pairs.
-/

namespace Erdos85

set_option maxHeartbeats 10000000

/-- Decidable bundle of the arithmetic conditions on one articulation side. -/
def orderNineArticulationSideAdmissible
    (e : Fin 6) (k : Fin 10) (b₁ b₂ b₃ : Fin 10) : Prop :=
  e.1 ≠ 0 ∧
  8 ≤ e.1 + 5 * k.1 ∧
  (7 * e.1 + 25 * k.1) % 2 = 0 ∧
  7 * e.1 + 25 * k.1 ≤
    (e.1 + 5 * k.1) * (e.1 + 5 * k.1 - 1) ∧
  e.1 + 8 * k.1 < 78 ∧
  b₁.1 + b₂.1 + b₃.1 = 3 * k.1 ∧
  orderNineNearRegularCutLower
    (e.1 + 8 * k.1) b₁.1 b₂.1 b₃.1 ≤ (e.1 : ℤ) ∧
  orderNineNearRegularCutLower
    (78 - (e.1 + 8 * k.1))
    (10 - b₁.1) (10 - b₂.1) (10 - b₃.1) ≤ (e.1 : ℤ)

instance (e : Fin 6) (k : Fin 10) (b₁ b₂ b₃ : Fin 10) :
    Decidable (orderNineArticulationSideAdmissible e k b₁ b₂ b₃) := by
  unfold orderNineArticulationSideAdmissible
  infer_instance

/-- Exact bounded classification of one possible articulation side.  The
hypotheses are equations (13)--(14) and the two boundary-`e` cut inequalities
from the q=9 near-regular cut audit. -/
theorem orderNine_articulation_side_parameter_classification
    (e : Fin 6) (k : Fin 10) (b₁ b₂ b₃ : Fin 10)
    (he : e.1 ≠ 0)
    (hn₀ : 8 ≤ e.1 + 5 * k.1)
    (hparity : (7 * e.1 + 25 * k.1) % 2 = 0)
    (hsimple : 7 * e.1 + 25 * k.1 ≤
      (e.1 + 5 * k.1) * (e.1 + 5 * k.1 - 1))
    (hproper : e.1 + 8 * k.1 < 78)
    (hbeta : b₁.1 + b₂.1 + b₃.1 = 3 * k.1)
    (hcut : orderNineNearRegularCutLower
      (e.1 + 8 * k.1) b₁.1 b₂.1 b₃.1 ≤ e.1)
    (hcutCompl : orderNineNearRegularCutLower
      (78 - (e.1 + 8 * k.1))
      (10 - b₁.1) (10 - b₂.1) (10 - b₃.1) ≤ e.1) :
    (e.1 = 2 ∧ k.1 = 2) ∨
    (e.1 = 2 ∧ k.1 = 4) ∨
    (e.1 = 2 ∧ k.1 = 6) ∨
    (e.1 = 3 ∧ k.1 = 3) ∨
    (e.1 = 3 ∧ k.1 = 5) ∨
    (e.1 = 3 ∧ k.1 = 7) ∨
    (e.1 = 4 ∧ k.1 = 6) ∨
    (e.1 = 4 ∧ k.1 = 8) ∨
    (e.1 = 5 ∧ k.1 = 3) ∨
    (e.1 = 5 ∧ k.1 = 7) ∨
    (e.1 = 5 ∧ k.1 = 9) := by
  have hterminal :
      ∀ (e : Fin 6) (k : Fin 10) (b₁ b₂ b₃ : Fin 10),
        orderNineArticulationSideAdmissible e k b₁ b₂ b₃ →
        (e.1 = 2 ∧ k.1 = 2) ∨
        (e.1 = 2 ∧ k.1 = 4) ∨
        (e.1 = 2 ∧ k.1 = 6) ∨
        (e.1 = 3 ∧ k.1 = 3) ∨
        (e.1 = 3 ∧ k.1 = 5) ∨
        (e.1 = 3 ∧ k.1 = 7) ∨
        (e.1 = 4 ∧ k.1 = 6) ∨
        (e.1 = 4 ∧ k.1 = 8) ∨
        (e.1 = 5 ∧ k.1 = 3) ∨
        (e.1 = 5 ∧ k.1 = 7) ∨
        (e.1 = 5 ∧ k.1 = 9) := by
    set_option maxHeartbeats 10000000 in
    set_option maxRecDepth 100000 in
      decide
  apply hterminal e k b₁ b₂ b₃
  exact ⟨he, hn₀, hparity, hsimple, hproper, hbeta, hcut, hcutCompl⟩

/-- The projected `(e,k)` type list produced by the side classifier. -/
def orderNineArticulationSideParameterType (e k : ℕ) : Prop :=
  (e = 2 ∧ k = 2) ∨ (e = 2 ∧ k = 4) ∨
  (e = 2 ∧ k = 6) ∨ (e = 3 ∧ k = 3) ∨
  (e = 3 ∧ k = 5) ∨ (e = 3 ∧ k = 7) ∨
  (e = 4 ∧ k = 6) ∨ (e = 4 ∧ k = 8) ∨
  (e = 5 ∧ k = 3) ∨ (e = 5 ∧ k = 7) ∨
  (e = 5 ∧ k = 9)

theorem two_le_of_orderNineArticulationSideParameterType
    {e k : ℕ} (h : orderNineArticulationSideParameterType e k) : 2 ≤ e := by
  unfold orderNineArticulationSideParameterType at h
  rcases h with h | h | h | h | h | h | h | h | h | h | h <;> omega

/-- Two articulation sides exhausting the five exceptional vertices and the
nine balance units have one of the three order pairs found by the exact
checker. -/
theorem orderNine_two_articulation_side_orders
    (e₀ k₀ e₁ k₁ : ℕ)
    (h₀ :
      (e₀ = 2 ∧ k₀ = 2) ∨ (e₀ = 2 ∧ k₀ = 4) ∨
      (e₀ = 2 ∧ k₀ = 6) ∨ (e₀ = 3 ∧ k₀ = 3) ∨
      (e₀ = 3 ∧ k₀ = 5) ∨ (e₀ = 3 ∧ k₀ = 7) ∨
      (e₀ = 4 ∧ k₀ = 6) ∨ (e₀ = 4 ∧ k₀ = 8) ∨
      (e₀ = 5 ∧ k₀ = 3) ∨ (e₀ = 5 ∧ k₀ = 7) ∨
      (e₀ = 5 ∧ k₀ = 9))
    (h₁ :
      (e₁ = 2 ∧ k₁ = 2) ∨ (e₁ = 2 ∧ k₁ = 4) ∨
      (e₁ = 2 ∧ k₁ = 6) ∨ (e₁ = 3 ∧ k₁ = 3) ∨
      (e₁ = 3 ∧ k₁ = 5) ∨ (e₁ = 3 ∧ k₁ = 7) ∨
      (e₁ = 4 ∧ k₁ = 6) ∨ (e₁ = 4 ∧ k₁ = 8) ∨
      (e₁ = 5 ∧ k₁ = 3) ∨ (e₁ = 5 ∧ k₁ = 7) ∨
      (e₁ = 5 ∧ k₁ = 9))
    (he : e₀ + e₁ = 5) (hk : k₀ + k₁ = 9) :
    (e₀ + 8 * k₀ = 18 ∧ e₁ + 8 * k₁ = 59) ∨
    (e₀ + 8 * k₀ = 59 ∧ e₁ + 8 * k₁ = 18) ∨
    (e₀ + 8 * k₀ = 27 ∧ e₁ + 8 * k₁ = 50) ∨
    (e₀ + 8 * k₀ = 50 ∧ e₁ + 8 * k₁ = 27) ∨
    (e₀ + 8 * k₀ = 34 ∧ e₁ + 8 * k₁ = 43) ∨
    (e₀ + 8 * k₀ = 43 ∧ e₁ + 8 * k₁ = 34) := by
  rcases h₀ with h₀ | h₀ | h₀ | h₀ | h₀ | h₀ | h₀ | h₀ | h₀ | h₀ | h₀ <;>
    rcases h₁ with h₁ | h₁ | h₁ | h₁ | h₁ | h₁ | h₁ | h₁ | h₁ | h₁ | h₁ <;>
    rcases h₀ with ⟨rfl, rfl⟩ <;>
    rcases h₁ with ⟨rfl, rfl⟩
  all_goals omega

/-- Any finite articulation decomposition exhausting the five exceptional
vertices has exactly two components.  Their orders lie in the three sharp
pairs `(18,59)`, `(27,50)`, `(34,43)`. -/
theorem orderNine_articulation_component_assembly
    {I : Type*} [DecidableEq I]
    (L : Finset I) (e k : I → ℕ)
    (hcard : 2 ≤ L.card)
    (htype : ∀ i ∈ L, orderNineArticulationSideParameterType (e i) (k i))
    (hesum : ∑ i ∈ L, e i = 5)
    (hksum : ∑ i ∈ L, k i = 9) :
    ∃ a b : I, a ≠ b ∧ L = {a, b} ∧
      ((e a + 8 * k a = 18 ∧ e b + 8 * k b = 59) ∨
       (e a + 8 * k a = 59 ∧ e b + 8 * k b = 18) ∨
       (e a + 8 * k a = 27 ∧ e b + 8 * k b = 50) ∨
       (e a + 8 * k a = 50 ∧ e b + 8 * k b = 27) ∨
       (e a + 8 * k a = 34 ∧ e b + 8 * k b = 43) ∨
       (e a + 8 * k a = 43 ∧ e b + 8 * k b = 34)) := by
  classical
  have hsumLower : 2 * L.card ≤ ∑ i ∈ L, e i := by
    calc
      2 * L.card = ∑ _i ∈ L, 2 := by simp [Nat.mul_comm]
      _ ≤ ∑ i ∈ L, e i := by
        apply Finset.sum_le_sum
        intro i hi
        exact two_le_of_orderNineArticulationSideParameterType (htype i hi)
  have hcardEq : L.card = 2 := by
    rw [hesum] at hsumLower
    omega
  obtain ⟨a, b, hab, hL⟩ := Finset.card_eq_two.mp hcardEq
  have heab : e a + e b = 5 := by
    simpa [hL, hab] using hesum
  have hkab : k a + k b = 9 := by
    simpa [hL, hab] using hksum
  have ha := htype a (by simp [hL])
  have hb := htype b (by simp [hL])
  unfold orderNineArticulationSideParameterType at ha hb
  refine ⟨a, b, hab, hL, ?_⟩
  exact orderNine_two_articulation_side_orders
    (e a) (k a) (e b) (k b) ha hb heab hkab

#print axioms orderNine_articulation_side_parameter_classification
#print axioms orderNine_two_articulation_side_orders
#print axioms orderNine_articulation_component_assembly

end Erdos85
