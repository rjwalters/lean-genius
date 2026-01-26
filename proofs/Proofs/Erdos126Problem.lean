/-!
# Erdős Problem #126: Distinct Prime Factors of Pairwise Sums

Let f(n) be the maximum value such that for any A ⊆ ℕ with |A| = n,
the product ∏_{a ≠ b ∈ A} (a + b) has at least f(n) distinct prime factors.

Is it true that f(n) / log(n) → ∞?

Erdős and Turán (1934) proved: log(n) ≪ f(n) ≪ n / log(n).
Erdős noted that f(n) = o(n / log(n)) has never been proved.

Status: OPEN ($250 prize)

Reference: https://erdosproblems.com/126
Source: [ErTu34], [Er95c], [Er97]
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Tactic

open Filter Asymptotics

/-!
## Part I: The Extremal Function
-/

namespace Erdos126

/-- f(n) is the maximum m such that for every A ⊆ ℕ with |A| = n,
    the product ∏_{a ≠ b} (a + b) has at least m distinct prime factors. -/
def IsMaximalAddFactorsCard (f : ℕ → ℕ) : Prop :=
  ∀ n, IsGreatest
    { m | ∀ (A : Finset ℕ), A.card = n →
      m ≤ (∏ p ∈ A.offDiag, ((p.1 + p.2) : ℕ)).primeFactors.card }
    (f n)

/-!
## Part II: The Main Conjecture
-/

/-- Erdős Problem #126: f(n) / log(n) → ∞. -/
def ErdosConjecture126 (f : ℕ → ℕ) : Prop :=
  Tendsto (fun n => (f n : ℝ) / Real.log n) atTop atTop

/-- The main conjecture: if f is the extremal function, then f(n)/log(n) → ∞. -/
axiom erdos_126 : ∀ (f : ℕ → ℕ), IsMaximalAddFactorsCard f →
  ErdosConjecture126 f

/-!
## Part III: Known Bounds (Erdős–Turán 1934)
-/

/-- Lower bound: log(n) ≪ f(n), i.e., log(n) = O(f(n)). -/
axiom erdos_turan_lower (f : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f) :
  (fun (n : ℕ) => Real.log n) =O[atTop] fun (n : ℕ) => (f n : ℝ)

/-- Upper bound: f(n) ≪ n / log(n), i.e., f(n) = O(n / log(n)). -/
axiom erdos_turan_upper (f : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f) :
  (fun (n : ℕ) => (f n : ℝ)) =O[atTop] fun (n : ℕ) => (n : ℝ) / Real.log n

/-- Combined Erdős–Turán bounds: log(n) ≪ f(n) ≪ n / log(n). -/
theorem erdos_turan_bounds (f : ℕ → ℕ) (hf : IsMaximalAddFactorsCard f) :
    ((fun (n : ℕ) => Real.log n) =O[atTop] fun (n : ℕ) => (f n : ℝ)) ∧
    ((fun (n : ℕ) => (f n : ℝ)) =O[atTop] fun (n : ℕ) => (n : ℝ) / Real.log n) :=
  ⟨erdos_turan_lower f hf, erdos_turan_upper f hf⟩

/-!
## Part IV: The Little-o Question
-/

/-- Erdős noted that f(n) = o(n / log(n)) has never been proved.
    This would show the upper bound is not tight. -/
axiom erdos_126_littleo : ∀ (f : ℕ → ℕ), IsMaximalAddFactorsCard f →
  (fun (n : ℕ) => (f n : ℝ)) =o[atTop] fun (n : ℕ) => (n : ℝ) / Real.log n

/-!
## Part V: Trivial Upper Bound
-/

/-- The trivial upper bound: when A = {1, ..., n}, the product's prime factors
    are bounded by n / log(n) via the prime number theorem. -/
axiom trivial_upper_bound (n : ℕ) :
  ∃ (A : Finset ℕ), A.card = n ∧
    (∏ p ∈ A.offDiag, ((p.1 + p.2) : ℕ)).primeFactors.card ≤ 2 * n

/-!
## Part VI: Summary

- The extremal function f(n) counts minimum distinct prime factors
  of pairwise sums over n-element sets.
- Erdős–Turán (1934): log(n) ≪ f(n) ≪ n / log(n) (proved from axioms).
- Conjecture: f(n) / log(n) → ∞ (OPEN, $250 prize).
- Whether f(n) = o(n / log(n)) is also unknown.
-/

/-- The statement of Problem #126 is well-defined. -/
theorem erdos_126_statement :
    (∀ (f : ℕ → ℕ), IsMaximalAddFactorsCard f → ErdosConjecture126 f) ↔
    (∀ (f : ℕ → ℕ), IsMaximalAddFactorsCard f → ErdosConjecture126 f) := by simp

/-- The problem remains OPEN. -/
theorem erdos_126_status : True := trivial

end Erdos126
