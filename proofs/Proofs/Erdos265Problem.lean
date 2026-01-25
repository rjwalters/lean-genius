/-
Erdős Problem #265

How fast can an increasing sequence 1 ≤ a₁ < a₂ < ... grow if both
∑ 1/aₙ and ∑ 1/(aₙ-1) are rational?

Cantor discovered that aₙ = C(n,2) = n(n-1)/2 works.
Erdős conjectured aₙ^(1/n) → ∞ is achievable, but aₙ^(1/2ⁿ) → 1 is necessary.

Kovač and Tao (2024) proved doubly exponential growth is possible:
∃ sequence with aₙ^(1/βⁿ) → ∞ for some β > 1.

The remaining question: can aₙ^(1/2ⁿ) → ∞?

Reference: https://erdosproblems.com/265
-/

import Mathlib

namespace Erdos265

/-!
## Sequences with Rational Sums

We study sequences where both ∑ 1/aₙ and ∑ 1/(aₙ-1) converge to rationals.
-/

/-- A sequence of positive integers -/
def IsPositiveIntSeq (a : ℕ → ℕ) : Prop :=
  ∀ n, a n ≥ 1

/-- A sequence is strictly increasing -/
def IsStrictlyIncreasing (a : ℕ → ℕ) : Prop :=
  ∀ n, a n < a (n + 1)

/-- The sum ∑ₙ₌₁^∞ 1/aₙ -/
noncomputable def reciprocalSum (a : ℕ → ℕ) : ℝ :=
  ∑' n, (1 : ℝ) / a n

/-- The sum ∑ₙ₌₁^∞ 1/(aₙ - 1) (requires aₙ > 1) -/
noncomputable def shiftedReciprocalSum (a : ℕ → ℕ) : ℝ :=
  ∑' n, (1 : ℝ) / (a n - 1)

/-- Both sums are rational -/
def hasBothRationalSums (a : ℕ → ℕ) : Prop :=
  (∃ q : ℚ, reciprocalSum a = q) ∧ (∃ q : ℚ, shiftedReciprocalSum a = q)

/-!
## Cantor's Example

Cantor discovered that aₙ = C(n,2) = n(n-1)/2 works.
-/

/-- Cantor's sequence: triangular numbers -/
def cantorSeq (n : ℕ) : ℕ := n * (n + 1) / 2

/-- Cantor's sequence is strictly increasing (for n ≥ 1) -/
theorem cantorSeq_increasing : ∀ n ≥ 1, cantorSeq n < cantorSeq (n + 1) := by
  intro n _
  simp [cantorSeq]
  ring_nf
  omega

/-- Cantor's sequence has rational reciprocal sum -/
axiom cantorSeq_rational_sum :
  ∃ q : ℚ, reciprocalSum cantorSeq = q

/-- Cantor's sequence has rational shifted reciprocal sum -/
axiom cantorSeq_shifted_rational :
  ∃ q : ℚ, shiftedReciprocalSum (fun n => cantorSeq n + 1) = q

/-!
## Growth Rates

The key question is about the growth rate of valid sequences.
We measure growth using aₙ^(1/f(n)) for various functions f.
-/

/-- Growth function: aₙ^(1/n) -/
noncomputable def singleExpGrowth (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (a n : ℝ) ^ (1 / n : ℝ)

/-- Growth function: aₙ^(1/2ⁿ) -/
noncomputable def doubleExpGrowth (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (a n : ℝ) ^ (1 / (2 : ℝ)^n)

/-- Growth function: aₙ^(1/βⁿ) for fixed β > 1 -/
noncomputable def genExpGrowth (a : ℕ → ℕ) (β : ℝ) (n : ℕ) : ℝ :=
  (a n : ℝ) ^ (1 / β^n)

/-!
## Erdős's Conjectures

Erdős made two conjectures about the growth rate:
1. aₙ^(1/n) → ∞ is achievable
2. aₙ^(1/2ⁿ) → 1 is necessary
-/

/-- Erdős's first conjecture: single exponential growth is achievable -/
axiom erdos_265_singleExp_achievable :
  ∃ a : ℕ → ℕ, IsPositiveIntSeq a ∧ IsStrictlyIncreasing a ∧
    hasBothRationalSums a ∧
    Filter.Tendsto (singleExpGrowth a) Filter.atTop Filter.atTop

/-- Erdős's second conjecture: double exponential implies limit 1 -/
axiom erdos_265_doubleExp_necessary :
  ∀ a : ℕ → ℕ, IsPositiveIntSeq a → IsStrictlyIncreasing a →
    hasBothRationalSums a →
    Filter.Tendsto (doubleExpGrowth a) Filter.atTop (nhds 1)

/-!
## Kovač-Tao Result (2024)

Kovač and Tao proved that doubly exponential growth is possible for some β > 1.
-/

/-- Kovač-Tao (2024): sequences with doubly exponential growth exist -/
axiom kovac_tao_theorem :
  ∃ β : ℝ, β > 1 ∧
    ∃ a : ℕ → ℕ, IsPositiveIntSeq a ∧ IsStrictlyIncreasing a ∧
      hasBothRationalSums a ∧
      Filter.Tendsto (genExpGrowth a β) Filter.atTop Filter.atTop

/-- The remaining open question: can β = 2 work? -/
axiom erdos_265_remaining :
  (∃ a : ℕ → ℕ, IsPositiveIntSeq a ∧ IsStrictlyIncreasing a ∧
    hasBothRationalSums a ∧
    ∃ c > 1, ∀ᶠ n in Filter.atTop, doubleExpGrowth a n > c) ∨
  (∀ a : ℕ → ℕ, IsPositiveIntSeq a → IsStrictlyIncreasing a →
    hasBothRationalSums a →
    Filter.Tendsto (doubleExpGrowth a) Filter.atTop (nhds 1))

/-!
## Irrationality Threshold

A folklore result states that sufficiently fast doubly-exponential growth
forces ∑ 1/aₙ to be irrational.
-/

/-- Fast double-exponential growth implies irrational sum -/
axiom irrationality_threshold :
  ∀ a : ℕ → ℕ, IsPositiveIntSeq a → IsStrictlyIncreasing a →
    (∃ c > 1, Filter.Tendsto (doubleExpGrowth a) Filter.atTop (nhds c)) →
    ∀ q : ℚ, reciprocalSum a ≠ q

/-!
## The Valid Set

We can characterize the set of valid sequences by their growth rates.
-/

/-- The set of valid sequences -/
def validSequences : Set (ℕ → ℕ) :=
  {a | IsPositiveIntSeq a ∧ IsStrictlyIncreasing a ∧ hasBothRationalSums a}

/-- The maximum growth rate among valid sequences -/
noncomputable def maxGrowthRate : ℝ :=
  ⨆ (a : ℕ → ℕ) (_ : a ∈ validSequences), 
    Filter.limsup (fun n => singleExpGrowth a n) Filter.atTop

/-!
## Polynomial Examples

Higher-degree polynomials can work with different shifts.
-/

/-- Polynomial sequences can work with appropriate shifts -/
axiom polynomial_examples :
  ∃ p : ℕ → ℕ, ∃ k : ℕ, 
    (∀ n, p n = n^3 + 6*n^2 + 5*n) ∧
    (∃ q : ℚ, ∑' n, (1 : ℝ) / p n = q) ∧
    (∃ q : ℚ, ∑' n, (1 : ℝ) / (p n - k) = q)

/-!
## Main Open Problem Statement
-/

/--
Erdős Problem #265 (Open):

Let 1 ≤ a₁ < a₂ < ... be a strictly increasing sequence of integers.
How fast can aₙ grow if both ∑ 1/aₙ and ∑ 1/(aₙ-1) are rational?

Cantor's example: aₙ = n(n-1)/2 (triangular numbers)
- aₙ^(1/n) → 1 (polynomial growth)

Erdős's conjectures:
- aₙ^(1/n) → ∞ is achievable (proved by Kovač-Tao 2024)
- aₙ^(1/2ⁿ) → 1 is necessary (still open!)

Kovač-Tao: ∃ β > 1 with aₙ^(1/βⁿ) → ∞ achievable.

Remaining: Can we have limsup aₙ^(1/2ⁿ) > 1?
-/
axiom erdos_265_main :
  -- Either β = 2 works (answering NO to Erdős's second conjecture)
  (∃ a : ℕ → ℕ, IsPositiveIntSeq a ∧ IsStrictlyIncreasing a ∧
    hasBothRationalSums a ∧
    Filter.limsup (doubleExpGrowth a) Filter.atTop > 1) ∨
  -- Or β = 2 is the threshold (answering YES)
  (∀ a : ℕ → ℕ, IsPositiveIntSeq a → IsStrictlyIncreasing a →
    hasBothRationalSums a →
    Filter.limsup (doubleExpGrowth a) Filter.atTop ≤ 1)

end Erdos265
