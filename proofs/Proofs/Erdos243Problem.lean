/-
Erdős Problem #243: Sylvester's Sequence Characterization

Let a₁ < a₂ < ⋯ be a strictly increasing sequence of positive integers such that:
  (1) lim_{n→∞} aₙ / aₙ₋₁² = 1
  (2) Σ (1/aₙ) ∈ ℚ (the sum of reciprocals is rational)

**Conjecture**: For all sufficiently large n, aₙ = aₙ₋₁² - aₙ₋₁ + 1.

This says that any sequence with these properties must eventually follow the
Sylvester recurrence. Sylvester's sequence (OEIS A000058) begins 2, 3, 7, 43, 1807, ...
and has Σ(1/aₙ) = 1.

**Status**: OPEN

**Historical Context**:
- Sylvester (1880) introduced the sequence and observed its unique properties
- Erdős-Straus (1964) proved partial results about the growth rate
- Badea (1993) proved related results for sequences summing to rationals
- The conjecture asks if the growth condition alone (with rational sum) forces Sylvester

Reference: https://erdosproblems.com/243
-/

import Mathlib

open Filter Topology BigOperators

namespace Erdos243

/- ## Sylvester's Sequence

The canonical example satisfying the hypotheses. Defined by:
  s₀ = 2
  sₙ₊₁ = sₙ² - sₙ + 1
-/

/-- Sylvester's sequence: 2, 3, 7, 43, 1807, ... -/
def sylvester : ℕ → ℕ
  | 0 => 2
  | n + 1 => sylvester n ^ 2 - sylvester n + 1

/-- First few values of Sylvester's sequence. -/
theorem sylvester_0 : sylvester 0 = 2 := rfl
theorem sylvester_1 : sylvester 1 = 3 := by native_decide
theorem sylvester_2 : sylvester 2 = 7 := by native_decide
theorem sylvester_3 : sylvester 3 = 43 := by native_decide
theorem sylvester_4 : sylvester 4 = 1807 := by native_decide

/-- Sylvester's sequence is strictly increasing (first values). -/
theorem sylvester_strictMono_small : sylvester 0 < sylvester 1 ∧
    sylvester 1 < sylvester 2 ∧ sylvester 2 < sylvester 3 := by native_decide

/- ## The Erdős Conjecture

A sequence satisfies the hypotheses if:
1. It is strictly monotone increasing
2. aₙ/aₙ₋₁² → 1 as n → ∞
3. The sum of reciprocals is rational
-/

/-- A sequence is eventually Sylvester if it satisfies the recurrence for large n. -/
def EventuallySylvester (a : ℕ → ℕ) : Prop :=
  ∀ᶠ n in atTop, a (n + 1) = a n ^ 2 - a n + 1

/-- The growth condition: aₙ/aₙ₋₁² → 1. -/
def HasSylvesterGrowth (a : ℕ → ℕ) : Prop :=
  Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1)

/-- The rationality condition: the sum of reciprocals is rational. -/
def HasRationalReciprocalSum (a : ℕ → ℕ) : Prop :=
  ∃ q : ℚ, Tendsto (fun N ↦ ∑ n ∈ Finset.range N, (1 : ℝ) / a n) atTop (𝓝 q)

/- ## Main Conjecture

Erdős Problem #243: If a strictly increasing sequence of positive integers has
Sylvester-type growth and rational reciprocal sum, it must eventually be Sylvester.

This is stated as an axiom since it remains an open problem.
-/

/-- **Erdős Problem #243** (Open Conjecture)

If a strictly monotone sequence of positive integers satisfies:
- lim aₙ₊₁/aₙ² = 1
- Σ(1/aₙ) converges to a rational number

Then eventually aₙ₊₁ = aₙ² - aₙ + 1 (the Sylvester recurrence).

This conjecture remains open. Erdős-Straus (1964) proved partial results,
and Badea (1993) proved related characterizations, but the full conjecture
in this generality is unresolved.
-/
axiom erdos_243 (a : ℕ → ℕ)
    (hMono : StrictMono a)
    (hPos : ∀ n, 0 < a n)
    (hGrowth : HasSylvesterGrowth a)
    (hRational : HasRationalReciprocalSum a) :
    EventuallySylvester a

/- ## Verification: Sylvester's Sequence Satisfies the Hypotheses

We verify that the canonical Sylvester sequence does satisfy all the hypotheses
(though proving convergence to 1 requires more machinery).
-/

/-- Sylvester's sequence consists of positive integers. -/
theorem sylvester_pos : ∀ n, 0 < sylvester n := by
  intro n
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [sylvester]
    omega

/-- The sum of reciprocals of Sylvester's sequence equals 1.

This is a classical result: 1/2 + 1/3 + 1/7 + 1/43 + ... = 1.
More precisely, for each n: Σᵢ₌₀ⁿ (1/sᵢ) = 1 - 1/(sₙ₊₁ - 1).
-/
axiom sylvester_sum_reciprocals :
    Tendsto (fun N ↦ ∑ n ∈ Finset.range N, (1 : ℝ) / sylvester n) atTop (𝓝 1)

/-- Sylvester's sequence has rational reciprocal sum (sum = 1). -/
theorem sylvester_hasRationalReciprocalSum : HasRationalReciprocalSum sylvester :=
  ⟨1, by convert sylvester_sum_reciprocals; simp⟩

end Erdos243
