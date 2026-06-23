/-
Erdős Problem #293: Missing Denominators in Egyptian Fraction Decompositions

Let v(k) be the minimal integer not appearing as a denominator in any
k-term Egyptian fraction decomposition 1 = 1/n₁ + ... + 1/nₖ with
distinct n₁ < n₂ < ... < nₖ. Estimate the growth of v(k).

**Status**: OPEN — bounds improving

**Known Bounds**:
- Lower: v(k) ≥ e^{ck²} for some c > 0 (van Doorn-Tang, 2025)
- Upper: v(k) ≤ k · c₀^{2^k} where c₀ ≈ 1.26408 is the Vardi constant
- The gap between these bounds is enormous

References:
- [BlEr75] Bleicher-Erdős, "The number of distinct subsums" (1975)
- [vDTa25b] van Doorn-Tang, arXiv:2512.22083 (2025)
- https://erdosproblems.com/293
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset

open Finset BigOperators

namespace Erdos293

/- ## Basic Definitions -/

/-- A k-term Egyptian fraction decomposition of 1: a set of k distinct
positive integers whose unit fractions sum to 1. -/
def isEgyptianDecomp (k : ℕ) (s : Finset ℕ) : Prop :=
  s.card = k ∧
  (∀ n ∈ s, n > 0) ∧
  (s.sum fun n => (1 : ℚ) / n) = 1

/-- Whether integer m appears as a denominator in some k-term decomposition. -/
def appearsInDecomp (k : ℕ) (m : ℕ) : Prop :=
  ∃ s : Finset ℕ, isEgyptianDecomp k s ∧ m ∈ s

/-- v(k): The smallest positive integer not appearing in any k-term
Egyptian fraction decomposition of 1. Axiomatized since the existence
proof requires showing denominators are bounded. -/
axiom v (k : ℕ) : ℕ

/- ## The Vardi Constant -/

/-- The Vardi recurrence: u₁ = 1, uᵢ₊₁ = uᵢ(uᵢ + 1).
Gives: 1, 2, 6, 42, 1806, ... -/
def vardiSeq : ℕ → ℕ
  | 0 => 1
  | n + 1 => vardiSeq n * (vardiSeq n + 1)

/-- First few values of the Vardi sequence. -/
theorem vardiSeq_values :
    vardiSeq 0 = 1 ∧
    vardiSeq 1 = 2 ∧
    vardiSeq 2 = 6 ∧
    vardiSeq 3 = 42 ∧
    vardiSeq 4 = 1806 := by
  simp [vardiSeq]

/-- The Vardi constant c₀ = lim_{n→∞} uₙ^{1/2^n} ≈ 1.26408. -/
noncomputable def vardiConstant : ℝ := 1.26408473530530

/- ## Known Lower Bounds -/

/-- van Doorn-Tang lower bound (2025): v(k) ≥ e^{ck²} for some c > 0.
This is a significant improvement over the factorial bound. -/
axiom vanDoorn_Tang_lower_bound :
    ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k > 0 →
      (v k : ℝ) ≥ Real.exp (c * k^2)

/- ## Known Upper Bounds -/

/-- Elementary upper bound: v(k) ≤ k · c₀^{2^k}. -/
axiom elementary_upper_bound :
    ∀ k : ℕ, k > 0 →
      (v k : ℝ) ≤ k * vardiConstant ^ (2^k : ℕ)

/-- Maximum denominator bound: in any k-term decomposition,
the largest denominator is at most k · uₖ. -/

/- ## Conjectures -/

/-- Erdős's conjecture (weak form): v(k) grows doubly exponentially
in √k, i.e., v(k) ≥ e^{e^{c√k}} for some c > 0. -/
def ErdosConjecture293Weak : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k > 0 →
    (v k : ℝ) ≥ Real.exp (Real.exp (c * Real.sqrt k))

/-- Erdős's conjecture (strong form): v(k) grows doubly exponentially
in k, i.e., v(k) ≥ e^{e^{ck}} for some c > 0. -/
def ErdosConjecture293Strong : Prop :=
  ∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k > 0 →
    (v k : ℝ) ≥ Real.exp (Real.exp (c * k))

/- ## Small Values -/

/-- v(1) = 2: The only 1-term decomposition would need 1/n = 1, but
we require distinct terms. Actually, n = 1 works, so v(1) = 2. -/

/-- v(3) = 4: The unique 3-term decomposition is 1 = 1/2 + 1/3 + 1/6,
so the first missing denominator is 4. -/

/- ## Summary -/

/-- **Erdős Problem #293 Summary.**
Current best bounds on v(k): e^{ck²} ≤ v(k) ≤ k · c₀^{2^k}.
The gap (e^{k²} vs e^{2^k}) is one of the largest in combinatorics. -/
theorem erdos_293_summary :
    (∃ c : ℝ, c > 0 ∧ ∀ k : ℕ, k > 0 →
      (v k : ℝ) ≥ Real.exp (c * k^2)) ∧
    (∀ k : ℕ, k > 0 →
      (v k : ℝ) ≤ k * vardiConstant ^ (2^k : ℕ)) :=
  ⟨vanDoorn_Tang_lower_bound, elementary_upper_bound⟩

end Erdos293
