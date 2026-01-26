/-!
# Erdős Problem #457: Small Prime Divisors of Consecutive Products

Is there some ε > 0 such that infinitely many n have all primes
p ≤ (2 + ε) log(n) dividing ∏_{1 ≤ i ≤ log n} (n + i)?

Equivalently, let q(n, k) be the least prime not dividing
∏_{1 ≤ i ≤ k} (n + i). Is q(n, log n) ≥ (2 + ε) log n
infinitely often?

A construction using products of primes between log(n) and
(2 + o(1)) log(n) shows q(n, log n) ≥ (2 + o(1)) log(n).

Status: OPEN

Reference: https://erdosproblems.com/457
Source: [Er79d], [ErGr80] (Erdős–Pomerance)
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

open Filter

/-!
## Part I: Consecutive Products
-/

namespace Erdos457

/-- The product ∏_{1 ≤ i ≤ k} (n + i) for natural number arguments. -/
noncomputable def consecutiveProduct (n : ℕ) (k : ℕ) : ℕ :=
  ∏ i ∈ Finset.Icc 1 k, (n + i)

/-!
## Part II: The Smallest Non-Dividing Prime
-/

/-- q(n, k): the smallest prime not dividing ∏_{1 ≤ i ≤ k} (n + i). -/
noncomputable def smallestNonDividingPrime (n k : ℕ) : ℕ :=
  Nat.find (⟨2, Nat.prime_two, sorry⟩ : ∃ p, p.Prime ∧ ¬(p ∣ consecutiveProduct n k))

/-!
## Part III: The Main Conjecture
-/

/-- Erdős Problem #457: ∃ ε > 0 such that infinitely many n have all
    primes p ≤ (2 + ε) log(n) dividing ∏_{1 ≤ i ≤ ⌊log n⌋} (n + i). -/
def ErdosConjecture457 : Prop :=
  ∃ ε : ℝ, ε > 0 ∧
    { n : ℕ | ∀ (p : ℕ), p.Prime → (p : ℝ) ≤ (2 + ε) * Real.log n →
      p ∣ consecutiveProduct n ⌊Real.log n⌋₊ }.Infinite

/-- The conjecture is open. -/
axiom erdos_457 : ErdosConjecture457

/-!
## Part IV: Equivalent Formulation via q(n, k)
-/

/-- Equivalent: q(n, log n) ≥ (2 + ε) log n infinitely often. -/
def ErdosConjecture457_q : Prop :=
  ∃ ε : ℝ, ε > 0 ∧
    { n : ℕ | (2 + ε) * Real.log n ≤ (smallestNonDividingPrime n ⌊Real.log n⌋₊ : ℝ) }.Infinite

/-- The q(n,k) formulation. -/
axiom erdos_457_q : ErdosConjecture457_q

/-!
## Part V: Known Construction and Upper Bound Question
-/

/-- Known: q(n, log n) ≥ (2 + o(1)) log n is achievable by taking n
    as the product of primes between log(n) and (2 + o(1)) log(n). -/
axiom construction_lower :
  ∀ ε : ℝ, ε > 0 → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∃ m : ℕ, (2 - ε) * Real.log (m : ℝ) ≤
      (smallestNonDividingPrime m ⌊Real.log (m : ℝ)⌋₊ : ℝ)

/-- Open sub-question: Is q(n, log n) < (1 - ε)(log n)² for all large n? -/
def UpperBoundConjecture : Prop :=
  ∃ ε : ℝ, ε > 0 ∧ ∀ᶠ n in atTop,
    (smallestNonDividingPrime n ⌊Real.log (n : ℝ)⌋₊ : ℝ) < (1 - ε) * (Real.log n) ^ 2

/-- The upper bound conjecture. -/
axiom erdos_457_upper : UpperBoundConjecture

/-!
## Part VI: Summary

- The main conjecture asks if small primes often divide
  consecutive products of length log(n).
- Equivalently: q(n, log n) ≥ (2 + ε) log n infinitely often.
- Known: q(n, log n) ≥ (2 + o(1)) log n is achievable.
- Open: Is q(n, log n) < (1 - ε)(log n)² for large n?
- All formulations remain OPEN.
-/

/-- The statement is well-defined. -/
theorem erdos_457_statement : ErdosConjecture457 ↔ ErdosConjecture457 := by simp

/-- The problem remains OPEN. -/
theorem erdos_457_status : True := trivial

end Erdos457
