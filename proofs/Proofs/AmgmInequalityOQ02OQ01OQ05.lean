/-
  Maclaurin Base Step: S₁² ≥ S₂

  Open Question (amgm-inequality-oq-02-oq-01-oq-05):
  For nonnegative reals x₁,…,xₙ (n ≥ 2), the first two Maclaurin averages satisfy
    S₁² ≥ S₂,
  where S₁ = e₁/n and S₂ = e₂/C(n,2), with
    e₁ = Σ xᵢ        (first elementary symmetric sum),
    e₂ = Σ_{i<j} xᵢxⱼ (second elementary symmetric sum).

  Strategy.
  • Newton-Girard (cf. parent oq-02-oq-01): e₁² = p₂ + 2 e₂, where p₂ = Σ xᵢ².
  • Power-mean / Cauchy-Schwarz: e₁² ≤ n · p₂.
  Clearing denominators, S₁² ≥ S₂ is equivalent to C(n,2)·e₁² ≥ n²·e₂, which after
  substituting 2 e₂ = e₁² - p₂ reduces to exactly n·p₂ ≥ e₁².

  No nonnegativity hypothesis on the xᵢ is actually needed: the inequality holds for
  all reals (it is a consequence of Cauchy-Schwarz). No sorries, no axioms.
-/
import Mathlib

namespace AmgmInequalityOQ02OQ01OQ05

open Finset BigOperators

variable (n : ℕ) (f : ℕ → ℝ)

/-- First elementary symmetric sum e₁ = Σ xᵢ. -/
def e1 : ℝ := ∑ i ∈ range n, f i

/-- Second power sum p₂ = Σ xᵢ². -/
def p2 : ℝ := ∑ i ∈ range n, (f i) ^ 2

/-- Second elementary symmetric sum e₂ = Σ_{i<j} xᵢxⱼ. -/
def e2 : ℝ := ∑ i ∈ range n, ∑ j ∈ range n, if i < j then f i * f j else 0

-- ============================================================
-- Newton-Girard: e₁² = p₂ + 2 e₂
-- ============================================================

/-- The full double sum splits, by trichotomy on the index pair, into the
    strictly-upper, diagonal, and strictly-lower triangular parts. -/
theorem double_sum_split :
    (∑ i ∈ range n, ∑ j ∈ range n, f i * f j)
      = (∑ i ∈ range n, ∑ j ∈ range n, if i < j then f i * f j else 0)
        + (∑ i ∈ range n, (f i) ^ 2)
        + (∑ i ∈ range n, ∑ j ∈ range n, if j < i then f i * f j else 0) := by
  have key : ∀ i ∈ range n,
      (∑ j ∈ range n, f i * f j)
        = (∑ j ∈ range n, if i < j then f i * f j else 0)
          + (f i) ^ 2
          + (∑ j ∈ range n, if j < i then f i * f j else 0) := by
    intro i hi
    have hdiag : (f i) ^ 2 = ∑ j ∈ range n, (if i = j then f i * f j else 0) := by
      rw [Finset.sum_ite_eq, if_pos hi]; ring
    rw [hdiag, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    rcases lt_trichotomy i j with h | h | h
    · simp [h, asymm h, Nat.ne_of_lt h]
    · subst h; simp
    · simp [h, asymm h, (Nat.ne_of_lt h).symm]
  rw [Finset.sum_congr rfl key, Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- The strictly-upper and strictly-lower triangular sums are equal (swap i,j). -/
theorem upper_eq_lower :
    (∑ i ∈ range n, ∑ j ∈ range n, if j < i then f i * f j else 0)
      = (∑ i ∈ range n, ∑ j ∈ range n, if i < j then f i * f j else 0) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : i < j
  · simp [h, mul_comm]
  · simp [h]

/-- Newton-Girard identity for the first two symmetric functions:
    e₁² = p₂ + 2 e₂. -/
theorem newton_girard : (e1 n f) ^ 2 = p2 n f + 2 * e2 n f := by
  unfold e1 p2 e2
  rw [sq, Finset.sum_mul_sum]
  rw [double_sum_split n f, upper_eq_lower n f]
  ring

-- ============================================================
-- Power-mean bound: e₁² ≤ n · p₂
-- ============================================================

/-- Cauchy-Schwarz / power-mean bound: (Σ xᵢ)² ≤ n · Σ xᵢ². -/
theorem sq_e1_le_card_mul_p2 : (e1 n f) ^ 2 ≤ (n : ℝ) * p2 n f := by
  unfold e1 p2
  have h := sq_sum_le_card_mul_sum_sq (s := range n) (f := f)
  simpa [Finset.card_range] using h

-- ============================================================
-- Maclaurin base step
-- ============================================================

/-- Cleared-denominator form: C(n,2)·e₁² ≥ n²·e₂.  Holds for all n. -/
theorem maclaurin_cleared :
    (n.choose 2 : ℝ) * (e1 n f) ^ 2 ≥ (n : ℝ) ^ 2 * e2 n f := by
  have hcs : (e1 n f) ^ 2 ≤ (n : ℝ) * p2 n f := sq_e1_le_card_mul_p2 n f
  have hng : (e1 n f) ^ 2 = p2 n f + 2 * e2 n f := newton_girard n f
  have hchoose : (n.choose 2 : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := Nat.cast_choose_two ℝ n
  -- 2·n·e₂ ≤ (n-1)·e₁²
  have hstar : 2 * (n : ℝ) * e2 n f ≤ ((n : ℝ) - 1) * (e1 n f) ^ 2 := by
    nlinarith [hcs, hng]
  rw [hchoose]
  nlinarith [hstar, (Nat.cast_nonneg n : (0 : ℝ) ≤ (n : ℝ)), sq_nonneg (e1 n f)]

/-- Maclaurin base step in averaged form: for n ≥ 2,
    S₁² ≥ S₂ with S₁ = e₁/n and S₂ = e₂/C(n,2). -/
theorem maclaurin_base_step (hn : 2 ≤ n) :
    ((e1 n f) / n) ^ 2 ≥ (e2 n f) / (n.choose 2 : ℝ) := by
  rw [ge_iff_le]
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hC : (0 : ℝ) < (n.choose 2 : ℝ) := by
    have : 0 < n.choose 2 := Nat.choose_pos (by omega)
    exact_mod_cast this
  rw [div_pow, div_le_div_iff₀ hC (pow_pos hn0 2)]
  nlinarith [maclaurin_cleared n f]

end AmgmInequalityOQ02OQ01OQ05
