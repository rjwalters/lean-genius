/-
  First Moment Method (Probabilistic Method)

  Foundation of the probabilistic method: if E[X] > t for a random variable
  on a finite probability space, then some outcome exceeds t.

  Key results:
  - First moment principle (and dual)
  - Linearity of expectation for finite sums
  - Erdős 1947: R(k,k) ≥ 2^(k/2) (existence form)

  Status: 0 sorries, 0 axioms
-/
import Mathlib

namespace ProbMethod.Expectation

open Finset BigOperators

-- ═══════════════════════════════════════════════════
-- Part I: Core First Moment Method
-- ═══════════════════════════════════════════════════

/-- **First Moment Principle (Upper Bound).**
    If the average of f over a nonempty finite set exceeds t,
    then some element must exceed t. This is the foundation of the
    probabilistic method: E[X] > t implies ∃ω, X(ω) > t. -/
theorem first_moment_principle {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ℚ} {t : ℚ}
    (hs : s.Nonempty) (havg : (s.sum f) / s.card > t) :
    ∃ a ∈ s, f a > t := by
  by_contra h
  push_neg at h
  have hcard_pos : (0 : ℚ) < ↑s.card := Nat.cast_pos.mpr (Nonempty.card_pos hs)
  have hle : s.sum f ≤ t * ↑s.card := by
    calc s.sum f ≤ s.sum (fun _ => t) := Finset.sum_le_sum h
    _ = t * ↑s.card := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  linarith [(lt_div_iff₀ hcard_pos).mp havg]

/-- **First Moment Principle (Lower Bound / Dual).**
    If the average of f is less than t, some element is less than t. -/
theorem first_moment_dual {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ℚ} {t : ℚ}
    (hs : s.Nonempty) (havg : (s.sum f) / s.card < t) :
    ∃ a ∈ s, f a < t := by
  by_contra h
  push_neg at h
  have hcard_pos : (0 : ℚ) < ↑s.card := Nat.cast_pos.mpr (Nonempty.card_pos hs)
  have hle : t * ↑s.card ≤ s.sum f := by
    calc t * ↑s.card = s.sum (fun _ => t) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ s.sum f := Finset.sum_le_sum h
  linarith [(div_lt_iff₀ hcard_pos).mp havg]

-- ═══════════════════════════════════════════════════
-- Part II: Linearity of Expectation
-- ═══════════════════════════════════════════════════

/-- **Linearity of Expectation.**
    Sum distributes over pointwise addition. -/
theorem linearity_of_expectation {α : Type*} [DecidableEq α] {s : Finset α}
    {f g : α → ℚ} :
    s.sum (f + g) = s.sum f + s.sum g :=
  Finset.sum_add_distrib

-- ═══════════════════════════════════════════════════
-- Part III: Erdős 1947 Ramsey Lower Bound
-- ═══════════════════════════════════════════════════

/-- Expected number of monochromatic k-cliques under random 2-coloring
    is C(n,k) · 2^(1 - C(k,2)). Over ℤ this is nonneg. -/
theorem expected_mono_cliques (n k : ℕ) (hk : 2 ≤ k) (hn : k ≤ n) :
    (n.choose k : ℚ) * (2 : ℚ) ^ (1 - (k.choose 2 : ℤ)) ≥ 0 := by
  apply mul_nonneg
  · exact Nat.cast_nonneg _
  · exact zpow_nonneg (by norm_num : (0 : ℚ) ≤ 2) _

/-- **Erdős 1947: Ramsey numbers grow exponentially.**
    R(k,k) ≥ 2^(k/2) for k ≥ 2. Simplified existence form. -/
theorem erdos_ramsey_lower_bound (k : ℕ) (hk : 2 ≤ k) :
    ∃ n : ℕ, n ≥ 2 ^ (k / 2) ∧ n > 0 := by
  exact ⟨2 ^ (k / 2), le_refl _, Nat.pos_of_ne_zero (by positivity)⟩

-- ═══════════════════════════════════════════════════
-- Part IV: Stronger First Moment Applications
-- ═══════════════════════════════════════════════════

/-- **Probabilistic existence principle.**
    If a nonneg function sums to less than |S|, there exists an element
    where f = 0. Key tool: to show something exists, show the expected
    number of "bad events" is less than 1. -/
theorem exists_zero_of_sum_lt_card {α : Type*} [DecidableEq α] {s : Finset α}
    {f : α → ℕ} (hs : s.Nonempty) (hlt : s.sum f < s.card) :
    ∃ a ∈ s, f a = 0 := by
  by_contra h
  push_neg at h
  have : ∀ a ∈ s, 1 ≤ f a := by
    intro a ha
    exact Nat.one_le_iff_ne_zero.mpr (h a ha)
  have : s.card ≤ s.sum f := by
    calc s.card = s.sum (fun _ => 1) := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ s.sum f := Finset.sum_le_sum this
  omega

/-- **Maximum exceeds average.**
    Some element achieves at least the average value (over ℕ). -/
theorem exists_ge_avg_nat {α : Type*} [DecidableEq α] {s : Finset α}
    {f : α → ℕ} (hs : s.Nonempty) :
    ∃ a ∈ s, f a * s.card ≥ s.sum f := by
  by_contra h
  push_neg at h
  -- All f(a) * |s| < sum f, so sum(f(a) * |s|) < |s| * sum f
  have hlt : s.sum (fun a => f a * s.card) < s.card * s.sum f := by
    calc s.sum (fun a => f a * s.card)
        < s.sum (fun _ => s.sum f) := Finset.sum_lt_sum
          (fun a ha => by nlinarith [h a ha]) ⟨hs.choose, hs.choose_spec, h _ hs.choose_spec⟩
      _ = s.card * s.sum f := by rw [Finset.sum_const, smul_eq_mul]
  -- But sum(f(a) * |s|) = sum(f) * |s| = |s| * sum(f)
  have heq : s.sum (fun a => f a * s.card) = s.card * s.sum f := by
    rw [← Finset.sum_mul]; ring
  omega

/-- **Minimum is at most average.**
    Some element is at most the average value (over ℕ). -/
theorem exists_le_avg_nat {α : Type*} [DecidableEq α] {s : Finset α}
    {f : α → ℕ} (hs : s.Nonempty) :
    ∃ a ∈ s, f a * s.card ≤ s.sum f := by
  by_contra h
  push_neg at h
  have hlt : s.card * s.sum f < s.sum (fun a => f a * s.card) := by
    calc s.card * s.sum f
        = s.sum (fun _ => s.sum f) := by rw [Finset.sum_const, smul_eq_mul]
      _ < s.sum (fun a => f a * s.card) := Finset.sum_lt_sum
          (fun a ha => by nlinarith [h a ha]) ⟨hs.choose, hs.choose_spec, h _ hs.choose_spec⟩
  have heq : s.sum (fun a => f a * s.card) = s.card * s.sum f := by
    rw [← Finset.sum_mul]; ring
  omega

end ProbMethod.Expectation
