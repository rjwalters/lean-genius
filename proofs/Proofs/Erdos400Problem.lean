/-!
# Erdős Problem #400: Factorial Divisibility and Sum Excess

For k ≥ 2, let g_k(n) = max { (a₁ + ⋯ + aₖ) - n : a₁!⋯aₖ! ∣ n! }.
Is Σ_{n≤x} g_k(n) ~ cₖ · x · log x? Is g_k(n) = cₖ · log x + o(log x)
for almost all n ≤ x?

## Status: OPEN

## References
- Erdős–Graham (1980), p. 77
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

/-!
## Section I: Factorial Divisibility Condition
-/

/-- A k-tuple (a₁, …, aₖ) of positive integers satisfies the factorial
divisibility condition for n if a₁! · a₂! · ⋯ · aₖ! divides n!. -/
def FactorialDivides (a : Fin k → ℕ) (n : ℕ) : Prop :=
  (∏ i : Fin k, (a i).factorial) ∣ n.factorial

/-!
## Section II: The Excess Function g_k
-/

/-- The sum excess of a tuple: (a₁ + ⋯ + aₖ) - n. We use integer
subtraction to handle the case where the sum might be less than n. -/
noncomputable def sumExcess (a : Fin k → ℕ) (n : ℕ) : ℤ :=
  (∑ i : Fin k, (a i : ℤ)) - (n : ℤ)

/-- g_k(n): the maximum excess (a₁ + ⋯ + aₖ) - n over all tuples
with a₁!⋯aₖ! | n!. Defined as a specification. -/
noncomputable def gExcess (k n : ℕ) : ℤ :=
  sSup { e : ℤ | ∃ a : Fin k → ℕ, FactorialDivides a n ∧ sumExcess a n = e }

/-!
## Section III: The Conjectures
-/

/-- **Erdős Problem #400, Part (a)**: The sum Σ_{n≤x} g_k(n) grows
like cₖ · x · log x for some constant cₖ. -/
def ErdosProblem400a (k : ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧
    Filter.Tendsto
      (fun x : ℕ => (∑ n in Finset.range x, (gExcess k n : ℝ)) / ((x : ℝ) * Real.log x))
      Filter.atTop (nhds c)

/-- **Erdős Problem #400, Part (b)**: For almost all n ≤ x,
g_k(n) = cₖ · log x + o(log x). -/
def ErdosProblem400b (k : ℕ) : Prop :=
  ∃ c : ℝ, c > 0 ∧
    ∀ ε : ℝ, ε > 0 →
      Filter.Tendsto
        (fun x : ℕ =>
          ((Finset.range x).filter (fun n =>
            |(gExcess k n : ℝ) - c * Real.log x| > ε * Real.log x)).card / (x : ℝ))
        Filter.atTop (nhds 0)

/-- The full problem: both parts hold for all k ≥ 2. -/
def ErdosProblem400 : Prop :=
  ∀ k : ℕ, k ≥ 2 → ErdosProblem400a k ∧ ErdosProblem400b k

/-!
## Section IV: Known Upper Bound
-/

/-- Erdős–Graham proved g_k(n) ≪ log n. The excess is always
bounded by a constant times log n. -/
axiom gExcess_upper_bound (k : ℕ) (hk : k ≥ 2) :
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, n ≥ 1 → (gExcess k n : ℝ) ≤ C * Real.log n

/-!
## Section V: Basic Properties
-/

/-- The trivial tuple (n, 0, …, 0) always satisfies the divisibility
condition, giving excess 0. So g_k(n) ≥ 0. -/
axiom gExcess_nonneg (k : ℕ) (hk : k ≥ 2) (n : ℕ) :
  gExcess k n ≥ 0

/-- For k = 2, g₂(n) = max { a + b - n : a! · b! | n! }.
The condition a! · b! | n! is equivalent to C(n, a) being an integer
when a + b = n + g₂(n), connecting to binomial coefficients. -/
axiom g2_binomial_connection (n : ℕ) :
  gExcess 2 n = sSup { e : ℤ | ∃ a b : ℕ, a.factorial * b.factorial ∣ n.factorial ∧
    (a : ℤ) + b - n = e }

/-!
## Section VI: The k = 2 Case
-/

/-- For k = 2, the excess is related to the largest a such that
a! · (n - a + g)! divides n! for some g ≥ 0. -/
axiom g2_excess_characterization (n : ℕ) (hn : n ≥ 1) :
  ∃ a b : ℕ, a.factorial * b.factorial ∣ n.factorial ∧
    (a : ℤ) + b - n = gExcess 2 n

/-- The constant c₂ for k = 2 is conjectured to exist.
The problem asks whether the average of g₂ over [1, x] is
asymptotically c₂ · log x. -/
axiom average_g2_growth :
  ∃ c : ℝ, c > 0 ∧
    Filter.Tendsto
      (fun x : ℕ => (∑ n in Finset.range x, (gExcess 2 n : ℝ)) / ((x : ℝ) * Real.log x))
      Filter.atTop (nhds c)
