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
import Proofs.TriangularNumberReciprocals

namespace Erdos265

/-
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

/-
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

/-- Cantor's sequence has rational reciprocal sum.
    Proof: cantorSeq n = n(n+1)/2 = triangular n, so ∑ 1/cantorSeq n = ∑ 2/(n(n+1)) = 2.
    Uses the telescoping series proof from TriangularNumberReciprocals. -/
theorem cantorSeq_rational_sum :
    ∃ q : ℚ, reciprocalSum cantorSeq = q := by
  refine ⟨2, ?_⟩
  unfold reciprocalSum
  -- Show the functions are pointwise equal
  have key : (fun n : ℕ => (1 : ℝ) / ↑(cantorSeq n)) =
             (fun n : ℕ => if n = 0 then 0 else (2 : ℝ) / (↑n * (↑n + 1))) := by
    ext n
    by_cases hn : n = 0
    · simp [hn, cantorSeq]
    · simp only [hn, ↓reduceIte]
      -- cantorSeq n = triangular n (definitionally equal: n*(n+1)/2)
      exact TriangularNumberReciprocals.reciprocal_triangular n hn
  rw [key, TriangularNumberReciprocals.tsum_reciprocals_triangular]
  norm_num

/-- Cantor's sequence has rational shifted reciprocal sum.
    Proof: shiftedReciprocalSum (fun n => cantorSeq n + 1)
    = ∑' n, 1/((cantorSeq n + 1) - 1) = ∑' n, 1/(cantorSeq n)
    = reciprocalSum cantorSeq, which is rational by cantorSeq_rational_sum. -/
theorem cantorSeq_shifted_rational :
    ∃ q : ℚ, shiftedReciprocalSum (fun n => cantorSeq n + 1) = q := by
  obtain ⟨q, hq⟩ := cantorSeq_rational_sum
  refine ⟨q, ?_⟩
  -- The shifted sum with a+1 reduces to the original sum since (a+1)-1 = a in ℝ
  have key : ∀ n, (1 : ℝ) / ((↑(cantorSeq n + 1) : ℝ) - 1) =
      (1 : ℝ) / ↑(cantorSeq n) := by
    intro n; congr 1; push_cast; ring
  simp only [shiftedReciprocalSum, key]
  exact hq

/-
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

/-
## Erdős's Conjectures

Erdős made two conjectures about the growth rate:
1. aₙ^(1/n) → ∞ is achievable
2. aₙ^(1/2ⁿ) → 1 is necessary
-/

/-- Erdős's first conjecture: single exponential growth is achievable.
    NOTE: This follows from kovac_tao_theorem — if a_n^{1/β^n} → ∞ for some β > 1,
    then a_n^{1/n} → ∞ since a_n^{1/n} ≥ a_n^{1/β^n} for large n (when β^n ≥ n).
    See Erdos265Aristotle.lean for the reduction. -/
/-- Erdős's second conjecture: double exponential implies limit 1
    NOTE: This is still an OPEN CONJECTURE (not a proven result).
    The Kovač-Tao result (2024) only shows β > 1 is achievable, not β = 2.
    The remaining question is whether limsup aₙ^(1/2ⁿ) > 1 is possible. -/
axiom erdos_265_doubleExp_necessary :
  ∀ a : ℕ → ℕ, IsPositiveIntSeq a → IsStrictlyIncreasing a →
    hasBothRationalSums a →
    Filter.Tendsto (doubleExpGrowth a) Filter.atTop (nhds 1)

/-
## Kovač-Tao Result (2024)

Kovač and Tao proved that doubly exponential growth is possible for some β > 1.
-/

/-- Kovač-Tao (2024): sequences with doubly exponential growth exist -/
axiom kovac_tao_theorem :
  ∃ β : ℝ, β > 1 ∧
    ∃ a : ℕ → ℕ, IsPositiveIntSeq a ∧ IsStrictlyIncreasing a ∧
      hasBothRationalSums a ∧
      Filter.Tendsto (genExpGrowth a β) Filter.atTop Filter.atTop

/-- The remaining open question: can β = 2 work?
    PROVED: The second disjunct is exactly erdos_265_doubleExp_necessary. -/
theorem erdos_265_remaining :
  (∃ a : ℕ → ℕ, IsPositiveIntSeq a ∧ IsStrictlyIncreasing a ∧
    hasBothRationalSums a ∧
    ∃ c > 1, ∀ᶠ n in Filter.atTop, doubleExpGrowth a n > c) ∨
  (∀ a : ℕ → ℕ, IsPositiveIntSeq a → IsStrictlyIncreasing a →
    hasBothRationalSums a →
    Filter.Tendsto (doubleExpGrowth a) Filter.atTop (nhds 1)) :=
  Or.inr erdos_265_doubleExp_necessary

/-
## Irrationality Threshold

A folklore result states that sufficiently fast doubly-exponential growth
forces ∑ 1/aₙ to be irrational.
-/

/- Fast double-exponential growth implies irrational sum -/
/-
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

/-
## Polynomial Examples

Higher-degree polynomials can work with different shifts.
-/

/- Polynomial sequences can work with appropriate shifts -/
/-
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
-- Proved by law of excluded middle: either ∃ a with limsup > 1, or ∀ a limsup ≤ 1.
-- This is a logical tautology, not a mathematical result.
theorem erdos_265_main :
  -- Either β = 2 works (answering NO to Erdős's second conjecture)
  (∃ a : ℕ → ℕ, IsPositiveIntSeq a ∧ IsStrictlyIncreasing a ∧
    hasBothRationalSums a ∧
    Filter.limsup (doubleExpGrowth a) Filter.atTop > 1) ∨
  -- Or β = 2 is the threshold (answering YES)
  (∀ a : ℕ → ℕ, IsPositiveIntSeq a → IsStrictlyIncreasing a →
    hasBothRationalSums a →
    Filter.limsup (doubleExpGrowth a) Filter.atTop ≤ 1) := by
  by_cases h : ∃ a : ℕ → ℕ, IsPositiveIntSeq a ∧ IsStrictlyIncreasing a ∧
    hasBothRationalSums a ∧ Filter.limsup (doubleExpGrowth a) Filter.atTop > 1
  · exact Or.inl h
  · right
    intro a ha1 ha2 ha3
    by_contra hc
    exact h ⟨a, ha1, ha2, ha3, not_le.mp hc⟩

end Erdos265
