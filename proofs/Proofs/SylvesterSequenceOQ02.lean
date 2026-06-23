import Mathlib

/-!
# Sylvester's sequence OQ-02: the reciprocals sum exactly to `1`

Sylvester's sequence is `a₀ = 2`, `a_{n+1} = aₙ² - aₙ + 1`, giving `2, 3, 7, 43, 1807, …`.

The base entry `SylvesterSequenceOQ01` proves the closed-form **partial** sum
`∑_{k=0}^{n} 1/aₖ = 1 - 1/(a_{n+1} - 1)` and remarks that "since `a_{n+1} - 1 → ∞`,
the infinite sum of reciprocals equals `1`" — but stops short of formalizing that
limit. This file closes that gap: it proves the genuine **infinite series** identity

* `syl_tsum_reciprocal` : `∑' k, 1/aₖ = 1`  (over `ℝ`), and
* `syl_reciprocal_hasSum` : `HasSum (fun k => 1/aₖ) 1`,

together with the two analytic ingredients it rests on:

* `syl_ge_add_two` : the linear lower bound `n + 2 ≤ aₙ` (so `aₙ → ∞`), and
* `syl_summable` : the reciprocal series is summable (partial sums bounded by `1`).

The series is unconditionally convergent because each tail term is positive and the
partial sums `1 - 1/(a_{n+1}-1)` are bounded above by `1`; the value is pinned down by
the telescoping closed form together with `1/(a_{n+1}-1) → 0`, which in turn follows
from the elementary linear bound `aₙ ≥ n + 2`. (Sylvester's sequence in fact grows
doubly exponentially, but a linear lower bound is all the convergence argument needs.)

The file is self-contained: the sequence and the few elementary facts about it
(`syl_succ`, `two_le_syl`, `syl_cast_succ`) are re-derived here so the analytic
capstone depends only on `Mathlib`.

No axioms, no sorries.
-/

namespace SylvesterSequenceOQ02

open Filter Topology

/-- Sylvester's sequence: `a₀ = 2`, `a_{n+1} = aₙ² - aₙ + 1`. -/
def syl : ℕ → ℕ
  | 0 => 2
  | (n + 1) => syl n ^ 2 - syl n + 1

@[simp] theorem syl_zero : syl 0 = 2 := rfl

theorem syl_succ (n : ℕ) : syl (n + 1) = syl n ^ 2 - syl n + 1 := rfl

/-- Every term is at least `2`. -/
theorem two_le_syl (n : ℕ) : 2 ≤ syl n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h : syl k + 2 ≤ syl k ^ 2 := by nlinarith [ih]
    rw [syl_succ]
    omega

/-- The recurrence, lifted to `ℤ` (no truncated subtraction). -/
theorem syl_cast_succ (n : ℕ) :
    (syl (n + 1) : ℤ) = (syl n : ℤ) ^ 2 - (syl n : ℤ) + 1 := by
  have h1 : syl n ≤ syl n ^ 2 := by nlinarith [two_le_syl n]
  rw [syl_succ]
  push_cast [Nat.cast_sub h1]
  ring

/-- **Linear lower bound** `n + 2 ≤ aₙ`. Each step gains at least one because
`a_{n+1} - aₙ = (aₙ-1)² ≥ 1`. This is far weaker than the true doubly-exponential
growth, but it is exactly what the convergence argument needs (`aₙ → ∞`). -/
theorem syl_ge_add_two : ∀ n, n + 2 ≤ syl n
  | 0 => by simp
  | (k + 1) => by
      have hk := two_le_syl k
      have ih := syl_ge_add_two k
      have h : syl k + syl k ≤ syl k ^ 2 := by nlinarith [hk]
      rw [syl_succ]
      omega

/-- The real-valued telescoping per-term identity (the `ℝ` analogue of `syl_recip_term`):
`1/aₙ = 1/(aₙ-1) - 1/(a_{n+1}-1)`. -/
theorem syl_real_recip_term (n : ℕ) :
    (1 : ℝ) / (syl n : ℝ)
      = 1 / ((syl n : ℝ) - 1) - 1 / ((syl (n + 1) : ℝ) - 1) := by
  have ha : (2 : ℝ) ≤ (syl n : ℝ) := by exact_mod_cast two_le_syl n
  have hsucc : (syl (n + 1) : ℝ) = (syl n : ℝ) ^ 2 - (syl n : ℝ) + 1 := by
    exact_mod_cast syl_cast_succ n
  have h0 : (syl n : ℝ) ≠ 0 := by linarith
  have h1 : (syl n : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (syl n : ℝ) ^ 2 - (syl n : ℝ) + 1 - 1 ≠ 0 := by nlinarith [ha]
  rw [hsucc]
  field_simp
  ring

/-- Closed form for real partial sums: `∑_{k≤n} 1/aₖ = 1 - 1/(a_{n+1}-1)`. -/
theorem syl_real_partial_sum (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (syl k : ℝ)
      = 1 - 1 / ((syl (n + 1) : ℝ) - 1) := by
  induction n with
  | zero =>
    rw [Finset.sum_range_one]
    norm_num [show syl 0 = 2 from rfl, show syl (0 + 1) = 3 from rfl]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, syl_real_recip_term (m + 1)]
    ring

/-- The error term vanishes: `1/(a_{n+1}-1) → 0`. The linear bound `aₙ ≥ n+2` squeezes
the positive error term below `1/(n+1) → 0`. -/
theorem syl_recip_pred_tendsto_zero :
    Tendsto (fun n => 1 / ((syl (n + 1) : ℝ) - 1)) atTop (𝓝 0) := by
  apply squeeze_zero (g := fun n : ℕ => 1 / ((n : ℝ) + 1))
  · intro n
    have h2 : (2 : ℝ) ≤ (syl (n + 1) : ℝ) := by exact_mod_cast two_le_syl (n + 1)
    exact one_div_nonneg.mpr (by linarith)
  · intro n
    have hb : (n + 1 + 2 : ℕ) ≤ syl (n + 1) := syl_ge_add_two (n + 1)
    have h1 : ((n : ℝ) + 1) ≤ (syl (n + 1) : ℝ) - 1 := by
      have hc : ((n + 1 + 2 : ℕ) : ℝ) ≤ (syl (n + 1) : ℝ) := by exact_mod_cast hb
      push_cast at hc; linarith
    exact one_div_le_one_div_of_le (by positivity) h1
  · exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- **Partial sums converge to `1`**: `∑_{k≤n} 1/aₖ → 1`. -/
theorem syl_partial_tendsto_one :
    Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (syl k : ℝ))
      atTop (𝓝 1) := by
  have hfun : (fun n => ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (syl k : ℝ))
      = fun n => 1 - 1 / ((syl (n + 1) : ℝ) - 1) := by
    funext n; exact syl_real_partial_sum n
  rw [hfun]
  have : Tendsto (fun n => 1 - 1 / ((syl (n + 1) : ℝ) - 1)) atTop (𝓝 (1 - 0)) :=
    Tendsto.const_sub 1 syl_recip_pred_tendsto_zero
  simpa using this

/-- **The reciprocal series is summable.** Every term is nonnegative and every partial
sum equals `1 - 1/(a_{n+1}-1) ≤ 1`, so the partial sums are bounded above by `1`. -/
theorem syl_summable : Summable (fun k => (1 : ℝ) / (syl k : ℝ)) := by
  apply summable_of_sum_range_le (c := 1)
  · intro n; exact one_div_nonneg.mpr (Nat.cast_nonneg _)
  · intro n
    cases n with
    | zero => simp
    | succ m =>
      rw [syl_real_partial_sum m]
      have h2 : (2 : ℝ) ≤ (syl (m + 1) : ℝ) := by exact_mod_cast two_le_syl (m + 1)
      have hpos : 0 ≤ 1 / ((syl (m + 1) : ℝ) - 1) := one_div_nonneg.mpr (by linarith)
      linarith

/-- **Sylvester's reciprocal series sums to exactly `1`:** `∑' k, 1/aₖ = 1`. -/
theorem syl_tsum_reciprocal : ∑' k, (1 : ℝ) / (syl k : ℝ) = 1 := by
  have hshift :
      Tendsto (fun n => ∑ k ∈ Finset.range (n + 1), (1 : ℝ) / (syl k : ℝ))
        atTop (𝓝 (∑' k, (1 : ℝ) / (syl k : ℝ))) :=
    syl_summable.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  exact tendsto_nhds_unique hshift syl_partial_tendsto_one

/-- **`HasSum` form** of the result: `HasSum (fun k => 1/aₖ) 1`. -/
theorem syl_reciprocal_hasSum : HasSum (fun k => (1 : ℝ) / (syl k : ℝ)) 1 :=
  (syl_summable.hasSum_iff).mpr syl_tsum_reciprocal

end SylvesterSequenceOQ02
