/-
  Erdős Problem #358: Sums of Consecutive Terms

  Source: https://erdosproblems.com/358
  Status: OPEN

  Statement:
  Let A = {a₁ < a₂ < ...} be an infinite sequence of integers.
  Let f(n) count the number of solutions to n = Σᵢ₌ᵤᵛ aᵢ (sum of consecutive terms).
  Is there such an A for which f(n) → ∞ as n → ∞?
  Or even where f(n) ≥ 2 for all large n?

  Background:
  - When A = {1, 2, 3, ...}, f(n) counts the number of odd divisors of n
  - Classical result: n can be expressed as sum of ≥2 consecutive positive integers iff n ≠ 2^k
  - In modern language: asks for convex set A with 1_A ∘ 1_A(n) → ∞
  - Erdős-Moser (1963): Considered A = primes, conjectured limsup is infinite

  References:
  - Guy, "Unsolved Problems in Number Theory", Problem C2
  - Erdős-Graham, "Old and new problems in combinatorial number theory" (1980)
  - Moser, "Notes on number theory III" (1963)

  Related: Problem #356 (finite analogue)
-/

import Mathlib

open Nat Filter Set BigOperators Finset

namespace Erdos358

/-! ## Part I: Definitions -/

/-- An infinite increasing sequence of integers. -/
structure IntSequence where
  seq : ℕ → ℤ
  increasing : ∀ n, seq n < seq (n + 1)

/-- The count of ways to express n as a sum of consecutive terms of A.
    f(n) = #{(u,v) : u ≤ v ∧ n = Σᵢ₌ᵤᵛ aᵢ} -/
noncomputable def consecutiveSumCount (A : IntSequence) (n : ℤ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | p.1 ≤ p.2 ∧
    (∑ i ∈ Finset.Icc p.1 p.2, A.seq i) = n}

/-! ## Part II: The Natural Numbers Case -/

/-- The natural numbers sequence: a_n = n+1. -/
def naturalsSeq : IntSequence where
  seq := fun n => (n + 1 : ℤ)
  increasing := fun n => by simp only [Int.lt_add_one_iff]; omega

/-- Sum of consecutive integers from u to v (inclusive). -/
def consecutiveSum (u v : ℕ) : ℤ :=
  ∑ i ∈ Finset.Icc u v, (i + 1 : ℤ)

/-- Formula for sum of consecutive integers: (v-u+1)(u+v+2)/2. -/
theorem consecutive_sum_formula (u v : ℕ) (huv : u ≤ v) :
    consecutiveSum u v = ((v - u + 1 : ℤ) * (u + v + 2)) / 2 := by
  sorry

/-- The classic result: n = sum of at least two consecutive positive integers
    if and only if n is not a power of 2. -/
theorem consecutive_sum_char (n : ℕ) (hn : n ≥ 3) :
    (∃ u v : ℕ, u < v ∧ n = ∑ i ∈ Finset.Icc (u+1) (v+1), i) ↔ ¬∃ k : ℕ, n = 2^k := by
  sorry

/-- For natural numbers, f(n) equals the number of odd divisors of n. -/
axiom naturals_count_odd_divisors (n : ℕ) (hn : n ≥ 1) :
    consecutiveSumCount naturalsSeq n = ((Nat.divisors n).filter Odd).card

/-! ## Part III: The Main Conjectures -/

/--
**Erdős Problem #358 (Strong Form)**:
Does there exist an infinite increasing sequence A such that
f(n) → ∞ as n → ∞?
-/
def Erdos358Strong : Prop :=
  ∃ A : IntSequence, Tendsto (fun n => (consecutiveSumCount A n : ℝ)) atTop atTop

/--
**Erdős Problem #358 (Weak Form)**:
Does there exist an infinite increasing sequence A such that
f(n) ≥ 2 for all sufficiently large n?
-/
def Erdos358Weak : Prop :=
  ∃ A : IntSequence, ∃ N₀ : ℤ, ∀ n ≥ N₀, consecutiveSumCount A n ≥ 2

/-- Strong implies weak. -/
axiom strong_implies_weak : Erdos358Strong → Erdos358Weak

/-! ## Part IV: Known Observations -/

/--
**Trivial observation (Egami):**
f(n) ≥ 1 for all large n is trivially achieved by A = naturals,
since every n ≥ 1 equals itself (the sum from n to n).
-/
theorem naturals_always_representable (n : ℕ) (hn : n ≥ 1) :
    consecutiveSumCount naturalsSeq n ≥ 1 := by
  sorry

/--
**The power of 2 obstruction:**
For A = naturals restricted to sums of ≥2 terms, powers of 2 have no representation.
This is the only obstruction.
-/
axiom power_of_two_obstruction :
    ∀ k : ℕ, ∀ u v : ℕ, u < v → (∑ i ∈ Finset.Icc (u+1) (v+1), i) ≠ 2^k

/-! ## Part V: The Prime Case -/

/-- The primes sequence (axiomatized since nth is complex). -/
axiom primesSeq : IntSequence
axiom primesSeq_def (n : ℕ) : primesSeq.seq n = Nat.nth Nat.Prime n

/--
**Erdős-Moser Conjecture (1963):**
When A = primes, the limsup of f(n) is infinite.
-/
def ErdosMoserConjecture : Prop :=
  ∀ M : ℕ, ∃ n : ℤ, consecutiveSumCount primesSeq n ≥ M

/-! ## Part VI: Weaker Questions

**Erdős-Moser observation:**
They could not even prove that the upper density of representable integers is positive.
-/

/-- Count of representable integers up to N. -/
noncomputable def representableCount (A : IntSequence) (N : ℤ) : ℕ :=
  Set.ncard {n : ℤ | n ≤ N ∧ consecutiveSumCount A n ≥ 1}

/--
**Density question:**
Does the upper density of integers representable as consecutive prime sums exist and is it positive?
-/
def PositiveDensityConjecture : Prop :=
  ∃ δ > 0, ∀ᶠ N in atTop, (representableCount primesSeq N : ℝ) / N ≥ δ

/-- We don't even know if the density is positive. -/
axiom density_unknown : PositiveDensityConjecture ∨ ¬PositiveDensityConjecture

/-! ## Part VII: Connection to Related Problems

**Connection to Problem #356:**
The finite analogue asks: how many integers up to x can be written as
sum of consecutive elements of a finite set?

**Convex sets:**
In modern additive combinatorics language, the problem asks about
convex sumsets (sums of arithmetic progressions within the set).
-/

/-! ## Part VIII: Current Status

**Erdős Problem #358: OPEN**

**Questions:**
1. (Strong) Does ∃ A with f(n) → ∞? — OPEN
2. (Weak) Does ∃ A with f(n) ≥ 2 for large n? — OPEN

**What's known:**
- For A = naturals: f(n) = #{odd divisors of n}, so f(n) → ∞ along highly composite numbers
- For A = naturals, sums of ≥2 terms: n representable iff n ≠ 2^k (CLASSICAL)
- For A = primes: Even positive density is unknown (OPEN)

**Erdős quote (1977):**
"This problem can perhaps be rightly criticized as being artificial and in the
backwater of Mathematics but it seems very strange and attractive to me."
-/
axiom erdos_358_open : Erdos358Strong ∨ ¬Erdos358Strong

/-! ## Part IX: Summary Theorems -/

/-- The problem status. -/
theorem erdos_358_status :
    (Erdos358Strong → Erdos358Weak) ∧
    (Erdos358Strong ∨ ¬Erdos358Strong) := by
  exact ⟨strong_implies_weak, erdos_358_open⟩

end Erdos358
