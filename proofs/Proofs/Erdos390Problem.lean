/-!
# Erdős Problem #390: Factorial Factorization with Large Factors

Let f(n) be the minimal m such that n! = a₁ · a₂ · ⋯ · aₖ with
n < a₁ < a₂ < ⋯ < aₖ = m. Is there a constant c such that
f(n) - 2n ~ c · n / log n?

## Status: OPEN

## References
- Erdős–Graham (1980), Old and New Problems and Results in Combinatorial Number Theory
- Erdős–Guy–Selfridge (1982), "Another property of 239 and some related questions"
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-!
## Section I: The Function f(n)
-/

/-- f(n) is the minimal largest factor m in any factorization n! = a₁⋯aₖ
with n < a₁ < ⋯ < aₖ = m. Axiomatized since the constructive definition
requires complex machinery. -/
axiom factorizationMax : ℕ → ℕ

/-- f(n) is well-defined and positive for n ≥ 3. -/
axiom factorizationMax_pos (n : ℕ) (hn : n ≥ 3) : factorizationMax n > 0

/-!
## Section II: Basic Lower Bound
-/

/-- f(n) ≥ 2n for all n ≥ 1. If n! = a₁⋯aₖ with all aᵢ > n, then
the product of k factors each > n is at least (n+1)⋯(2n), so the
largest factor must be at least 2n. -/
axiom factorizationMax_ge_2n (n : ℕ) (hn : n ≥ 1) :
  factorizationMax n ≥ 2 * n

/-!
## Section III: Erdős–Guy–Selfridge Bounds
-/

/-- Erdős–Guy–Selfridge (1982): f(n) - 2n ≍ n / log n. There exist
constants C > c > 0 such that c·n/log n ≤ f(n) - 2n ≤ C·n/log n
for all large n. -/
axiom factorizationMax_asymptotic :
  ∃ C c : ℝ, C > 0 ∧ c > 0 ∧
    ∀ n : ℕ, n ≥ 2 →
      c * n / Real.log n ≤ (factorizationMax n : ℝ) - 2 * n ∧
      (factorizationMax n : ℝ) - 2 * n ≤ C * n / Real.log n

/-!
## Section IV: The Conjecture
-/

/-- **Erdős Problem #390**: Does the limit
lim_{n→∞} (f(n) - 2n) · log(n) / n exist and equal some constant c > 0?

The Erdős–Guy–Selfridge bounds show this ratio stays bounded between
positive constants, but whether a specific limit exists is unknown. -/
def ErdosProblem390 : Prop :=
  ∃ c : ℝ, c > 0 ∧
    Filter.Tendsto
      (fun n : ℕ => ((factorizationMax n : ℝ) - 2 * n) * Real.log n / n)
      Filter.atTop (nhds c)

/-!
## Section V: Related Properties
-/

/-- The factorization exists: for large n, there exists a factorization
n! = a₁⋯aₖ with n < a₁ < ⋯ < aₖ. -/
axiom factorization_exists (n : ℕ) (hn : n ≥ 3) :
  ∃ (k : ℕ) (a : Fin k → ℕ),
    (∀ i, a i > n) ∧
    StrictMono a ∧
    (∏ i, a i) = n.factorial ∧
    a ⟨k - 1, by omega⟩ = factorizationMax n

/-- OEIS A193429 gives the first values of f(n). For example,
f(3) = 6 since 3! = 6 is the only factorization. -/
axiom factorizationMax_small_values :
  factorizationMax 3 = 6

/-!
## Section VI: Monotonicity and Growth
-/

/-- f is eventually monotone increasing: for large enough n,
f(n+1) ≥ f(n). -/
axiom factorizationMax_eventually_monotone :
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ →
    factorizationMax (n + 1) ≥ factorizationMax n

/-- The secondary term n/log n grows to infinity, showing f(n) - 2n → ∞. -/
axiom factorizationMax_excess_unbounded :
  Filter.Tendsto
    (fun n : ℕ => (factorizationMax n : ℝ) - 2 * n)
    Filter.atTop Filter.atTop
