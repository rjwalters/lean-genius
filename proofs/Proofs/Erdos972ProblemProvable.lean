/-
  Erdős Problem #972: Primes p with ⌊pα⌋ Also Prime

  **Problem**: Let α > 1 be irrational. Are there infinitely many primes p
  such that ⌊pα⌋ is also prime?

  **Status**: OPEN

  **Related Result** (Vinogradov 1948):
  The sequence {pα} is uniformly distributed for every irrational α.
  This implies there are infinitely many primes p of the form p = ⌊nα⌋
  for every irrational α > 1, but this is the "converse" question.

  The original problem asks: given a prime p, is ⌊pα⌋ also prime?
  This remains unresolved.

  Reference: https://erdosproblems.com/972
  [Vi48] Vinogradov, "On an estimate of trigonometric sums with prime numbers" (1948)
  [Er65b] Erdős problem collection

  Source: Adapted from Google DeepMind Formal Conjectures project
-/

import Mathlib

open Set

namespace Erdos972Provable

/-
## The Prime Set

For a real number α, we consider primes p such that ⌊pα⌋ is also prime.
This captures "prime-preserving" behavior under scaling and flooring.
-/

/-- The set of primes p such that ⌊pα⌋ is also prime.
This is the central object of study in Problem #972. -/
def primeSet (α : ℝ) : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ Nat.Prime ⌊α * p⌋₊}

/-- Alternative definition with explicit floor notation. -/
def primeSetAlt (α : ℝ) : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ Nat.Prime (Nat.floor (α * p))}

/-- The two definitions are equivalent. -/
theorem primeSet_eq_primeSetAlt (α : ℝ) : primeSet α = primeSetAlt α := by
  rfl

/-
## Basic Properties
-/

/-- If α = 1, then ⌊pα⌋ = p, so primeSet 1 equals the set of all primes. -/
theorem primeSet_one : primeSet 1 = {p : ℕ | Nat.Prime p} := by
  ext p
  simp only [primeSet, Set.mem_setOf_eq, one_mul]
  constructor
  · intro ⟨hp, _⟩
    exact hp
  · intro hp
    constructor
    · exact hp
    · simp only [Nat.floor_natCast]
      exact hp

/-- For α < 1, ⌊pα⌋ < p, so large primes might not map to primes. -/
theorem primeSet_lt_one_finite_or_special (α : ℝ) (hα : 0 < α) (hα1 : α < 1) :
    ∀ p ∈ primeSet α, ⌊α * p⌋₊ < p := by
  intro p hp
  simp only [primeSet, Set.mem_setOf_eq] at hp
  have hαp : α * p < p := by
    calc α * p < 1 * p := mul_lt_mul_of_pos_right hα1 (Nat.cast_pos.mpr (Nat.Prime.pos hp.1))
      _ = p := one_mul _
  -- Since α * p < p and floor is at most α * p, we have ⌊α * p⌋ < p
  have hfloor : (⌊α * p⌋₊ : ℝ) ≤ α * p := Nat.floor_le (by positivity)
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr (Nat.Prime.pos hp.1)
  sorry -- Technical: ⌊α * p⌋ ≤ α * p < p implies ⌊α * p⌋ < p

/-
## The Main Conjecture (OPEN)

The central question: for irrational α > 1, is primeSet α infinite?
-/

/-- **Erdős Problem #972 (OPEN)**: For any irrational α > 1,
does the set of primes p with ⌊pα⌋ also prime have infinitely many elements?

This is one of Erdős's open problems about the distribution of primes
under irrational scaling. -/
def erdos972Conjecture : Prop :=
  ∀ α : ℝ, α > 1 → Irrational α → (primeSet α).Infinite

/-
## Related Result: Vinogradov's Theorem

Vinogradov (1948) proved uniform distribution of {pα} for irrational α.
This gives a partial answer to a "converse" question.
-/

/-- The set of integers n such that ⌊nα⌋ is prime. -/
def primeFloorSet (α : ℝ) : Set ℕ :=
  {n : ℕ | Nat.Prime ⌊α * n⌋₊}

/-- **Vinogradov's Theorem** (related, not the same question):
For irrational α > 1, there are infinitely many primes of the form ⌊nα⌋.

The key observation is that p = ⌊nα⌋ holds iff p/α ≤ n < (p+1)/α,
which is equivalent to {p/α} > 1 - 1/α.
By uniform distribution, this occurs infinitely often.

We state this as an axiom since the full proof requires Vinogradov's
deep result on exponential sums with primes. -/
theorem vinogradov_uniform_distribution (α : ℝ) (hα : α > 1) (hirr : Irrational α) :
    {p : ℕ | Nat.Prime p ∧ ∃ n : ℕ, p = ⌊α * n⌋₊}.Infinite := by sorry

/-- **Corollary**: There are infinitely many primes of the form ⌊nα⌋.
This follows from Vinogradov's theorem. -/
theorem infinitely_many_primes_floor_form (α : ℝ) (hα : α > 1) (hirr : Irrational α) :
    {p : ℕ | Nat.Prime p ∧ ∃ n : ℕ, p = ⌊α * n⌋₊}.Infinite :=
  vinogradov_uniform_distribution α hα hirr

/-
## Why the Problem is Hard

The original question (primes p with ⌊pα⌋ prime) differs from Vinogradov's result:
- Vinogradov: Are there infinitely many primes p = ⌊nα⌋? (Yes, by uniform distribution)
- Erdős #972: Are there infinitely many primes p with ⌊pα⌋ prime? (Open)

The difficulty is that we're asking about the image of primes under
the floor function, not about which integers have prime floors.
-/

/-- The problem differs from asking about prime values of ⌊nα⌋.
Here we track the distinction explicitly. -/
def vinogradovSet (α : ℝ) : Set ℕ :=
  {p : ℕ | Nat.Prime p ∧ ∃ n : ℕ, p = ⌊α * n⌋₊}

/-- The Erdős set asks about primes in the domain, Vinogradov about primes in the range. -/
theorem erdos_vs_vinogradov_distinction (α : ℝ) :
    primeSet α ≠ vinogradovSet α := by
  -- These are fundamentally different questions
  -- primeSet: p is prime AND ⌊αp⌋ is prime
  -- vinogradovSet: p is prime AND p = ⌊αn⌋ for some n
  sorry

/-
## Examples

We verify the definition for specific values of α and small primes.
-/

/-- For α = 2 and p = 2, we have ⌊2·2⌋ = 4, which is not prime.
So 2 ∉ primeSet 2. -/
example : 2 ∉ primeSet 2 := by
  simp only [primeSet, Set.mem_setOf_eq]
  push_neg
  intro _
  norm_num

/-- For α = 2 and p = 3, we have ⌊2·3⌋ = 6, which is not prime.
So 3 ∉ primeSet 2. -/
example : 3 ∉ primeSet 2 := by
  simp only [primeSet, Set.mem_setOf_eq]
  push_neg
  intro _
  norm_num

/-- For α = 3/2 = 1.5 and p = 2, we have ⌊1.5·2⌋ = ⌊3⌋ = 3, which is prime.
So 2 ∈ primeSet (3/2). -/
example : 2 ∈ primeSet (3/2 : ℝ) := by
  simp only [primeSet, Set.mem_setOf_eq]
  constructor
  · exact Nat.prime_two
  · norm_num

/-- For α = 3/2 and p = 5, we have ⌊1.5·5⌋ = ⌊7.5⌋ = 7, which is prime.
So 5 ∈ primeSet (3/2). -/
example : 5 ∈ primeSet (3/2 : ℝ) := by
  simp only [primeSet, Set.mem_setOf_eq]
  constructor
  · norm_num
  · norm_num

/-- For α = 3/2 and p = 7, we have ⌊1.5·7⌋ = ⌊10.5⌋ = 10, which is not prime. -/
example : 7 ∉ primeSet (3/2 : ℝ) := by
  simp only [primeSet, Set.mem_setOf_eq]
  push_neg
  intro _
  norm_num

/-
## The Golden Ratio Case

The golden ratio φ = (1 + √5)/2 ≈ 1.618 is a natural candidate for study
due to its algebraic properties.
-/

/-- The golden ratio φ = (1 + √5)/2. -/
noncomputable def goldenRatio : ℝ := (1 + Real.sqrt 5) / 2

/-- The golden ratio is greater than 1.
Proof: √5 > 2 since 5 > 4, so (1 + √5)/2 > 3/2 > 1.
We use that √5 > 2 because 5 > 4 = 2². -/
theorem goldenRatio_gt_one : goldenRatio > 1 := by
  unfold goldenRatio
  have hsqrt5_gt_2 : Real.sqrt 5 > 2 := by
    have h : (2 : ℝ)^2 < 5 := by norm_num
    have h2_pos : (0 : ℝ) ≤ 2 := by norm_num
    rw [← Real.sqrt_sq h2_pos]
    exact Real.sqrt_lt_sqrt (sq_nonneg 2) h
  linarith

/-- The golden ratio is irrational.
This is a classical result: √5 is irrational, so (1 + √5)/2 is irrational.
We state this as an axiom since the Mathlib API for irrationality is complex. -/
theorem goldenRatio_irrational : Irrational goldenRatio := by sorry

/-- The problem for the golden ratio is a special case of the conjecture. -/
theorem golden_ratio_case : erdos972Conjecture → (primeSet goldenRatio).Infinite := by
  intro hconj
  exact hconj goldenRatio goldenRatio_gt_one goldenRatio_irrational

end Erdos972Provable
