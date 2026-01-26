/-!
# Erdős Problem 462: Least Prime Factor Sums in Short Intervals

Let `p(n)` denote the least prime factor of `n`. There exists `c > 0`
such that `∑_{n<x, n composite} p(n)/n ~ c · x^{1/2} / (log x)²`.

Does there exist `C > 0` such that
`∑_{x ≤ n ≤ x + C·x^{1/2}·(log x)²} p(n)/n ≫ 1`
for all sufficiently large `x`?

*Reference:* [erdosproblems.com/462](https://www.erdosproblems.com/462),
Erdős–Graham (1980), p. 92.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! ## Least prime factor -/

/-- The least prime factor of `n` (returns 0 for `n ≤ 1`). -/
noncomputable def leastPrimeFactor (n : ℕ) : ℕ :=
    if h : n ≤ 1 then 0
    else n.minFac

/-- For `n ≥ 2`, `leastPrimeFactor n` is prime. -/
axiom leastPrimeFactor_prime (n : ℕ) (hn : 2 ≤ n) :
    (leastPrimeFactor n).Prime

/-- `leastPrimeFactor n` divides `n` for `n ≥ 2`. -/
axiom leastPrimeFactor_dvd (n : ℕ) (hn : 2 ≤ n) :
    leastPrimeFactor n ∣ n

/-- `leastPrimeFactor n` is at most any prime dividing `n`. -/
axiom leastPrimeFactor_le (n p : ℕ) (hn : 2 ≤ n) (hp : p.Prime) (hpn : p ∣ n) :
    leastPrimeFactor n ≤ p

/-! ## Sums involving least prime factor -/

/-- Sum of `p(n)/n` over composites in `{2, …, x-1}`. -/
noncomputable def compositeSum (x : ℕ) : ℝ :=
    (Finset.Icc 2 (x - 1)).sum fun n =>
      if n.Prime then 0
      else (leastPrimeFactor n : ℝ) / (n : ℝ)

/-- Sum of `p(n)/n` over an interval `{a, …, b}`. -/
noncomputable def intervalSum (a b : ℕ) : ℝ :=
    (Finset.Icc a b).sum fun n =>
      (leastPrimeFactor n : ℝ) / (n : ℝ)

/-! ## Known asymptotics -/

/-- There exists `c > 0` such that `∑_{n<x, composite} p(n)/n ~ c·√x/(log x)²`.
We state a one-sided bound: the sum is `Θ(√x/(log x)²)`. -/
axiom compositeSum_asymptotic :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ c₁ ≤ c₂ ∧
      ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
        c₁ * (x : ℝ) ^ (1/2 : ℝ) / (Real.log x) ^ 2 ≤ compositeSum x ∧
        compositeSum x ≤ c₂ * (x : ℝ) ^ (1/2 : ℝ) / (Real.log x) ^ 2

/-! ## Main conjecture -/

/-- Erdős Problem 462: There exists `C > 0` such that the sum
`∑_{x ≤ n ≤ x + C·√x·(log x)²} p(n)/n` is bounded below by
an absolute constant for all large `x`. -/
def ErdosProblem462 : Prop :=
    ∃ C : ℝ, 0 < C ∧
      ∃ δ : ℝ, 0 < δ ∧
        ∃ x₀ : ℕ, ∀ x : ℕ, x₀ ≤ x →
          δ ≤ intervalSum x ⌊(x : ℝ) + C * (x : ℝ) ^ (1/2 : ℝ) * (Real.log x) ^ 2⌋₊

/-! ## Basic properties -/

/-- The least prime factor of a prime is itself. -/
axiom leastPrimeFactor_prime_self (p : ℕ) (hp : p.Prime) :
    leastPrimeFactor p = p

/-- The least prime factor of any `n ≥ 2` is at least 2. -/
axiom leastPrimeFactor_ge_two (n : ℕ) (hn : 2 ≤ n) :
    2 ≤ leastPrimeFactor n

/-- The least prime factor of any `n ≥ 2` is at most `√n`. -/
axiom leastPrimeFactor_le_sqrt (n : ℕ) (hn : 2 ≤ n) (hc : ¬n.Prime) :
    (leastPrimeFactor n : ℝ) ≤ (n : ℝ) ^ (1/2 : ℝ)
