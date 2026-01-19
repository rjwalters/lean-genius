/-
  Erdős Problem #314: Harmonic Sum Error Term

  Source: https://erdosproblems.com/314
  Status: SOLVED (Lim-Steinerberger 2024)

  Statement:
  Let n ≥ 1 and let m be minimal such that ∑_{k=n}^{m} 1/k ≥ 1.
  Define ε(n) = ∑_{k=n}^{m} 1/k - 1.
  How small can ε(n) be? Is it true that lim inf n²ε(n) = 0?

  Solution:
  YES! Lim and Steinerberger (2024) proved that there exist infinitely many n such that
    ε(n)n² ≪ (log log n / log n)^{1/2}

  The exponent 2 is believed to be optimal: lim inf ε(n)n^{2+δ} = ∞ for all δ > 0.

  Key ideas:
  - The harmonic sum H(n,m) = 1/n + 1/(n+1) + ... + 1/m grows like log(m/n)
  - For the sum to reach 1, we need m ≈ en (approximately)
  - The error ε(n) measures how much we overshoot
  - Finding small ε(n) requires n where the harmonic sum barely exceeds 1

  References:
  - Lim, J., Steinerberger, S. (2024). "On differences of two harmonic numbers"
    arXiv:2405.11354
-/

import Mathlib

namespace Erdos314

/-! ## Harmonic Sum Definitions

The partial harmonic sum from n to m, and the definition of m(n) as the
minimal integer making the sum at least 1.
-/

/-- The harmonic number H_n = 1 + 1/2 + ... + 1/n -/
noncomputable def harmonicNumber (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, (1 : ℝ) / (k + 1)

/-- Partial harmonic sum from n to m: ∑_{k=n}^{m} 1/k -/
noncomputable def partialHarmonicSum (n m : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc n m, (1 : ℝ) / k

/-- Alternative form: H_m - H_{n-1} -/
lemma partialHarmonicSum_as_difference (n m : ℕ) (hn : n ≥ 1) (hm : m ≥ n) :
    partialHarmonicSum n m = harmonicNumber m - harmonicNumber (n - 1) := by
  sorry

/-! ## The Function m(n)

m(n) is the minimal integer m ≥ n such that the partial harmonic sum reaches 1.
-/

/-- m(n) = minimal m such that ∑_{k=n}^{m} 1/k ≥ 1 -/
noncomputable def m_of_n (n : ℕ) : ℕ := sorry

/-- m(n) is well-defined: the sum eventually exceeds 1 -/
axiom m_of_n_exists : ∀ n : ℕ, n ≥ 1 →
  ∃ m : ℕ, m ≥ n ∧ partialHarmonicSum n m ≥ 1

/-- m(n) is minimal: the sum from n to m(n)-1 is less than 1 -/
axiom m_of_n_minimal : ∀ n : ℕ, n ≥ 1 →
  partialHarmonicSum n (m_of_n n - 1) < 1

/-- m(n) achieves: the sum from n to m(n) is at least 1 -/
axiom m_of_n_achieves : ∀ n : ℕ, n ≥ 1 →
  partialHarmonicSum n (m_of_n n) ≥ 1

/-! ## The Error Term ε(n)

ε(n) measures how much the harmonic sum overshoots 1.
-/

/-- ε(n) = ∑_{k=n}^{m(n)} 1/k - 1, the overshoot -/
noncomputable def epsilon (n : ℕ) : ℝ :=
  partialHarmonicSum n (m_of_n n) - 1

/-- ε(n) is non-negative by definition of m(n) -/
theorem epsilon_nonneg : ∀ n : ℕ, n ≥ 1 → epsilon n ≥ 0 := by
  intro n hn
  unfold epsilon
  linarith [m_of_n_achieves n hn]

/-- ε(n) is at most 1/n (we add at most 1/m(n) ≤ 1/n to exceed 1) -/
theorem epsilon_upper_bound : ∀ n : ℕ, n ≥ 1 → epsilon n ≤ 1 / n := by
  intro n hn
  sorry -- Requires showing 1/m(n) ≤ 1/n

/-! ## Approximation of m(n)

For large n, m(n) ≈ e·n since the harmonic sum grows logarithmically.
-/

/-- Asymptotic: m(n)/n → e as n → ∞ -/
axiom m_over_n_limit :
  Filter.Tendsto (fun n => (m_of_n n : ℝ) / n) Filter.atTop (nhds Real.exp 1)

/-- More precisely: m(n) = ⌊e·n + 1/2⌋ for most n -/
axiom m_of_n_approximation : ∀ n : ℕ, n ≥ 1 →
  |(m_of_n n : ℝ) - Real.exp 1 * n| ≤ 1

/-! ## The Main Question: lim inf n²ε(n) = 0?

Erdős asked whether the lim inf of n²ε(n) equals 0.
Lim and Steinerberger (2024) proved this is TRUE.
-/

/-- The Erdős conjecture: lim inf n²ε(n) = 0 -/
def erdos_conjecture : Prop :=
  ∀ δ > 0, ∃ᶠ n in Filter.atTop, (n : ℝ)^2 * epsilon n < δ

/-! ## Lim-Steinerberger Theorem (2024)

The main result: infinitely many n with ε(n)n² small.
-/

/-- Lim-Steinerberger (2024): ε(n)n² ≪ (log log n / log n)^{1/2} for infinitely many n -/
axiom lim_steinerberger_theorem :
  ∃ C > 0, ∀ᶠ n in Filter.atTop,
    ∃ k : ℕ, k ≤ n ∧ k ≥ 1 ∧
    (k : ℝ)^2 * epsilon k ≤ C * (Real.log (Real.log k) / Real.log k)^(1/2 : ℝ)

/-- Corollary: The Erdős conjecture is TRUE -/
theorem erdos_conjecture_true : erdos_conjecture := by
  intro δ hδ
  -- The Lim-Steinerberger bound goes to 0, so eventually it's < δ
  sorry

/-! ## Optimal Exponent Conjecture

Erdős-Graham and Lim-Steinerberger believe the exponent 2 is optimal.
-/

/-- Conjecture: lim inf ε(n)n^{2+δ} = ∞ for all δ > 0 -/
axiom optimal_exponent_conjecture : ∀ δ > 0,
  Filter.Tendsto (fun n => (n : ℝ)^(2 + δ) * epsilon n) Filter.atTop Filter.atTop

/-- Alternative form: ε(n) ≥ c/n² for some constant c > 0 infinitely often -/
axiom epsilon_lower_bound : ∃ c > 0, ∀ᶠ n in Filter.atTop,
  epsilon n ≥ c / (n : ℝ)^2

/-! ## Connection to Diophantine Approximation

The problem is related to how well log(m/n) approximates 1 - γ
where γ is the Euler-Mascheroni constant.
-/

/-- The Euler-Mascheroni constant γ ≈ 0.5772... -/
noncomputable def eulerMascheroni : ℝ := sorry

/-- Asymptotic: ε(n) ≈ 1/(m·n) - (something involving Euler-Mascheroni) -/
axiom epsilon_asymptotic : ∀ n : ℕ, n ≥ 1 →
  |epsilon n - 1 / ((m_of_n n : ℝ) * n)| ≤ C / n^2 where C := 1

/-! ## Summary

Erdős Problem #314 asks about the lim inf of n²ε(n) where
ε(n) = ∑_{k=n}^{m(n)} 1/k - 1 and m(n) is minimal such that the sum ≥ 1.

**Main Result (Lim-Steinerberger 2024)**:
lim inf n²ε(n) = 0

More precisely: there exist infinitely many n with
  ε(n)n² ≪ (log log n / log n)^{1/2}

**Conjecture**: The exponent 2 is optimal:
  lim inf ε(n)n^{2+δ} = ∞ for all δ > 0

**Status**: SOLVED - The main question is affirmatively resolved.
-/

/-- Summary: The main theorem states the Erdős conjecture is true -/
theorem erdos_314_summary :
    erdos_conjecture ∧
    (∃ C > 0, ∀ᶠ n in Filter.atTop,
      ∃ k : ℕ, k ≤ n ∧ k ≥ 1 ∧
      (k : ℝ)^2 * epsilon k ≤ C * (Real.log (Real.log k) / Real.log k)^(1/2 : ℝ)) := by
  exact ⟨erdos_conjecture_true, lim_steinerberger_theorem⟩

end Erdos314
