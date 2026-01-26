/-!
# Erdős Problem #825 — Abundancy Bound for Weird Numbers

Erdős Problem #825 asks: is there an absolute constant C > 0 such that every
integer n with σ(n) > C·n is the distinct sum of proper divisors of n?

A *weird number* is an abundant number that is not semiperfect (cannot be
expressed as a distinct sum of proper divisors). The problem asks whether
sufficiently high abundancy forces semiperfectness.

## Key results

- **Lower bound**: We must have C > 2, since 70 is weird with σ(70)/70 ≈ 2.06.
- **Conjectured value**: C = 3 may suffice.
- **Status**: Open. Erdős offered a $25 prize.

Reference: https://erdosproblems.com/825
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Rat.Basic
import Mathlib.Tactic

/-! ## Divisor-sum and proper divisors -/

/-- Sum of divisors σ(n). -/
noncomputable def divisorSum (n : ℕ) : ℕ :=
    (Finset.filter (· ∣ n) (Finset.range (n + 1))).sum id

/-- Proper divisors of n (divisors less than n). -/
def properDivisors (n : ℕ) : Finset ℕ :=
    Finset.filter (fun d => d ∣ n ∧ d < n) (Finset.range n)

/-- n is abundant if σ(n) > 2n. -/
def IsAbundant (n : ℕ) : Prop := 2 * n < divisorSum n

/-! ## Semiperfect and weird numbers -/

/-- n is semiperfect if it equals the sum of some subset of its proper divisors. -/
def IsSemiperfect (n : ℕ) : Prop :=
    ∃ S : Finset ℕ, S ⊆ properDivisors n ∧ S.sum id = n

/-- n is weird if it is abundant but not semiperfect. -/
def IsWeird (n : ℕ) : Prop := IsAbundant n ∧ ¬IsSemiperfect n

/-! ## Abundancy ratio -/

/-- The abundancy index σ(n)/n as a rational number. -/
noncomputable def abundancy (n : ℕ) (hn : 0 < n) : ℚ :=
    (divisorSum n : ℚ) / (n : ℚ)

/-! ## Known examples -/

/-- 70 is the smallest weird number. -/
axiom weird_70 : IsWeird 70

/-- σ(70) = 144, so abundancy of 70 is 144/70 ≈ 2.057. -/
axiom sigma_70 : divisorSum 70 = 144

/-! ## Lower bound on C -/

/-- If C works for the problem, then C > 2. The counterexample is n = 70:
    σ(70) = 144 > 2 · 70 = 140, yet 70 is not semiperfect. -/
axiom necessary_lower_bound (C : ℚ) (hC : 0 < C)
    (h : ∀ n : ℕ, 0 < n → C * (n : ℚ) < (divisorSum n : ℚ) → IsSemiperfect n) :
    2 < C

/-! ## Odd weird numbers -/

/-- No odd weird number is known. It is an open question (Erdős #470)
    whether any odd weird number exists. -/
axiom no_known_odd_weird :
    ∀ n : ℕ, n ≤ 10 ^ 21 → ¬(n % 2 = 1 ∧ IsWeird n)

/-- If no odd weird numbers exist, then all weird numbers have abundancy < 4. -/
axiom odd_weird_abundancy_bound :
    (∀ n : ℕ, n % 2 = 1 → ¬IsWeird n) →
      ∀ n : ℕ, 0 < n → IsWeird n → (divisorSum n : ℚ) < 4 * (n : ℚ)

/-! ## Main conjecture -/

/-- Erdős Problem 825: there exists an absolute constant C > 0 such that
    every n with σ(n) > C·n is semiperfect (i.e., the distinct sum of
    some of its proper divisors). Equivalently, weird numbers have
    bounded abundancy. -/
def ErdosProblem825 : Prop :=
    ∃ (C : ℚ), 2 < C ∧
      ∀ n : ℕ, 0 < n → C * (n : ℚ) < (divisorSum n : ℚ) → IsSemiperfect n

/-- Strengthened conjecture: C = 3 suffices. -/
def ErdosProblem825_C3 : Prop :=
    ∀ n : ℕ, 0 < n → 3 * (n : ℚ) < (divisorSum n : ℚ) → IsSemiperfect n
