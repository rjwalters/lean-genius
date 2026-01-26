/-!
# Erdős Problem #524: Maximum of Random Sign Polynomials

Erdős Problem #524 (Salem–Zygmund) asks for the correct order of magnitude of
M_n(t) = max_{x ∈ [-1,1]} |Σ_{k≤n} (-1)^{ε_k(t)} x^k| for almost all
t ∈ (0,1), where ε_k(t) are the binary digits of t.

Known bounds:
- Lower: M_n(t)/n^{1/2-ε} → ∞ a.e. for every ε > 0 (Erdős, unpublished)
- Upper: M_n(t) ≪ (n/log log n)^{1/2} for infinitely many n, a.e. (Chung)

The expected answer is M_n(t) ~ C√n for almost all t, analogous to the
classical Salem–Zygmund theorem for random trigonometric polynomials.

Reference: https://erdosproblems.com/524
-/

import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.Filter.Basic

/-! ## Definitions -/

/-- Binary digit function: the k-th digit in the binary expansion of t ∈ (0,1). -/
noncomputable def binaryDigit (t : ℝ) (k : ℕ) : ℤ :=
  if (⌊t * 2 ^ k⌋ % 2 : ℤ) = 0 then 1 else -1

/-- Random sign polynomial: P_n(t, x) = Σ_{k=1}^{n} sign_k(t) · x^k
    where sign_k(t) = (-1)^{ε_k(t)} is determined by binary digits of t. -/
noncomputable def randSignPoly (t : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k in Finset.range n, (binaryDigit t (k + 1) : ℝ) * x ^ (k + 1)

/-- M_n(t): the maximum modulus of the random sign polynomial on [-1,1]. -/
noncomputable def polyMax (t : ℝ) (n : ℕ) : ℝ :=
  sSup { |randSignPoly t n x| | x ∈ Set.Icc (-1 : ℝ) 1 }

/-! ## Known Lower Bound (Erdős) -/

/-- Erdős (unpublished): For almost all t ∈ (0,1) and every ε > 0,
    M_n(t)/n^{1/2-ε} → ∞ as n → ∞. This means M_n(t) grows at least
    almost as fast as √n. -/
axiom erdos_lower_bound :
  ∀ ε : ℝ, 0 < ε → ε < (1 : ℝ) / 2 →
    ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo (0 : ℝ) 1 →
      Filter.Tendsto (fun n : ℕ => polyMax t n / (n : ℝ) ^ ((1 : ℝ) / 2 - ε))
        Filter.atTop Filter.atTop

/-! ## Known Upper Bound (Chung) -/

/-- Chung: For almost all t ∈ (0,1), there exist infinitely many n such that
    M_n(t) ≤ C · √(n / log log n) for some absolute constant C. -/
axiom chung_upper_bound :
  ∃ C : ℝ, 0 < C ∧
    ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo (0 : ℝ) 1 →
      ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
        polyMax t n ≤ C * Real.sqrt ((n : ℝ) / Real.log (Real.log n))

/-! ## Classical Comparison: Salem–Zygmund for Trigonometric Polynomials -/

/-- Salem–Zygmund theorem (for comparison): for random trigonometric polynomials
    with ±1 coefficients, the maximum on [0,2π] is typically Θ(√(n log n)).
    The polynomial case on [-1,1] is expected to behave differently due to
    endpoint concentration. -/
axiom salem_zygmund_trigonometric :
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ c₁ < c₂ ∧
    ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        c₁ * Real.sqrt ((n : ℝ) * Real.log n) ≤ polyMax t n ∧
        polyMax t n ≤ c₂ * Real.sqrt ((n : ℝ) * Real.log n)

/-! ## Main Open Problem -/

/-- Erdős Problem #524: Determine the correct order of magnitude of M_n(t)
    for almost all t ∈ (0,1). The known bounds leave a gap between
    n^{1/2-ε} (lower) and √(n/log log n) (upper, for infinitely many n). -/
axiom erdos_524_order_of_magnitude :
  ∃ f : ℕ → ℝ, (∀ n, 0 < f n) ∧
    ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioo (0 : ℝ) 1 →
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
          c₁ * f n ≤ polyMax t n ∧ polyMax t n ≤ c₂ * f n
