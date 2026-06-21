import Mathlib

/-
# The Integral Test: Sum–Integral Comparison for Antitone Functions

For an antitone (non-increasing) function `f` on an interval, the definite
integral is sandwiched between the right-endpoint (lower) Riemann sum and the
left-endpoint (upper) Riemann sum:

  ∑_{i<a} f(x₀ + i + 1)  ≤  ∫_{x₀}^{x₀+a} f  ≤  ∑_{i<a} f(x₀ + i).

This is the engine behind the **integral test** for series convergence.  We
package the two one-sided Mathlib bounds (`AntitoneOn.sum_le_integral` and
`AntitoneOn.integral_le_sum`) into the single two-sided comparison, and then
apply it to `f(x) = 1/x` on `[1, n+1]` to obtain the classical logarithmic
bounds on the harmonic numbers:

  log(n + 1)  ≤  Hₙ        and        H_{n+1}  ≤  1 + log(n + 1),

so that `Hₙ - log(n+1)` stays in `[0, 1]` — the boundedness that defines the
Euler–Mascheroni constant and proves the harmonic series diverges only
logarithmically.

All results are fully machine-verified: 0 sorries, 0 axioms.
-/

namespace AntitoneIntegralSumComparison

open scoped BigOperators
open Finset intervalIntegral

/-! ## Part I — The general integral-test sandwich -/

/-- **Integral test sandwich.** For `f` antitone on `[x₀, x₀ + a]`, the integral
lies between the right Riemann sum (lower bound) and the left Riemann sum (upper
bound).  This is the two-sided comparison underlying the integral test. -/
theorem integral_sandwich {f : ℝ → ℝ} {x₀ : ℝ} {a : ℕ}
    (hf : AntitoneOn f (Set.Icc x₀ (x₀ + a))) :
    (∑ i ∈ Finset.range a, f (x₀ + (i + 1 : ℕ))) ≤ (∫ x in x₀..x₀ + a, f x) ∧
      (∫ x in x₀..x₀ + a, f x) ≤ ∑ i ∈ Finset.range a, f (x₀ + i) :=
  ⟨hf.sum_le_integral, hf.integral_le_sum⟩

/-! ## Part II — The harmonic numbers -/

/-- The `n`-th harmonic number `Hₙ = 1 + 1/2 + ⋯ + 1/n = ∑_{i<n} 1/(i+1)`. -/
noncomputable def harmonic (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, 1 / (i + 1 : ℝ)

@[simp] theorem harmonic_zero : harmonic 0 = 0 := by simp [harmonic]

/-- `x ↦ 1/x` is antitone on `[1, 1+n]` (it lives on the positive reals). -/
private theorem oneDiv_antitone (n : ℕ) :
    AntitoneOn (fun x : ℝ => 1 / x) (Set.Icc (1 : ℝ) (1 + n)) := by
  intro x hx y _ hxy
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx.1
  exact one_div_le_one_div_of_le hx0 hxy

/-- `∫₁^{1+n} 1/x dx = log(n + 1)`. -/
private theorem log_integral (n : ℕ) :
    (∫ x in (1 : ℝ)..(1 + (n : ℝ)), 1 / x) = Real.log ((n : ℝ) + 1) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1 + (n : ℝ)) :=
    Set.notMem_uIcc_of_lt one_pos (by positivity)
  rw [integral_one_div h0, div_one]
  congr 1
  ring

/-! ## Part III — Logarithmic bounds on the harmonic numbers -/

/-- **Lower bound.** `log(n + 1) ≤ Hₙ`.  Applying `integral_le_sum` to `1/x`:
the integral `log(n+1)` is at most the left Riemann sum `∑_{i<n} 1/(i+1) = Hₙ`. -/
theorem log_le_harmonic (n : ℕ) : Real.log ((n : ℝ) + 1) ≤ harmonic n := by
  have key := (oneDiv_antitone n).integral_le_sum
  rw [log_integral n] at key
  refine key.trans_eq ?_
  unfold harmonic
  apply Finset.sum_congr rfl
  intro i _
  rw [add_comm (1 : ℝ) (i : ℝ)]

/-- **Upper bound.** `H_{n+1} ≤ 1 + log(n + 1)`.  Applying `sum_le_integral` to
`1/x`: the right Riemann sum `∑_{i<n} 1/(i+2) = H_{n+1} - 1` is at most the
integral `log(n+1)`. -/
theorem harmonic_succ_le (n : ℕ) : harmonic (n + 1) ≤ 1 + Real.log ((n : ℝ) + 1) := by
  have key := (oneDiv_antitone n).sum_le_integral
  rw [log_integral n] at key
  push_cast at key
  -- rewrite the right Riemann sum into `∑_{i<n} 1/(i+2)`
  have hsum : (∑ i ∈ Finset.range n, 1 / (1 + ((i : ℝ) + 1)))
      = ∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 2) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ring
  rw [hsum] at key
  -- and `H_{n+1} = (∑_{i<n} 1/(i+2)) + 1`
  have hH : harmonic (n + 1) = (∑ i ∈ Finset.range n, 1 / ((i : ℝ) + 2)) + 1 := by
    unfold harmonic
    rw [Finset.sum_range_succ']
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      congr 1
      push_cast
      ring
    · norm_num
  rw [hH]
  linarith [key]

/-! ## Part IV — Boundedness of `Hₙ - log(n+1)` (Euler–Mascheroni) -/

/-- `Hₙ - log(n + 1) ≥ 0` for every `n`. -/
theorem harmonic_sub_log_nonneg (n : ℕ) : 0 ≤ harmonic n - Real.log ((n : ℝ) + 1) := by
  linarith [log_le_harmonic n]

/-- `H_{n+1} - log(n + 1) ≤ 1` for every `n`.  Together with the previous bound,
`Hₙ - log(n+1)` is trapped in `[0, 1]`, the boundedness behind the
Euler–Mascheroni constant `γ = lim (Hₙ - log n) ∈ (0, 1)`. -/
theorem harmonic_succ_sub_log_le_one (n : ℕ) :
    harmonic (n + 1) - Real.log ((n : ℝ) + 1) ≤ 1 := by
  linarith [harmonic_succ_le n]

/-! ## Part V — Worked witnesses -/

/-- `H₃ = 1 + 1/2 + 1/3 = 11/6`. -/
example : harmonic 3 = 11 / 6 := by
  unfold harmonic
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero]
  norm_num

/-- The lower bound instantiated at `n = 3`: `log 4 ≤ H₃`. -/
example : Real.log ((3 : ℝ) + 1) ≤ harmonic 3 := log_le_harmonic 3

/-- The sandwich specialised to `1/x` on `[1, 1+n]`: the harmonic Riemann sums
trap the logarithmic integral. -/
example (n : ℕ) :
    (∑ i ∈ Finset.range n, 1 / ((1 : ℝ) + (i + 1 : ℕ))) ≤
      (∫ x in (1 : ℝ)..(1 + n), 1 / x) ∧
    (∫ x in (1 : ℝ)..(1 + n), 1 / x) ≤ ∑ i ∈ Finset.range n, 1 / ((1 : ℝ) + i) :=
  integral_sandwich (oneDiv_antitone n)

end AntitoneIntegralSumComparison
