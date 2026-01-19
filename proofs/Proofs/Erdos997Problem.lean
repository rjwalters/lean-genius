/-
Erdős Problem #997: Well-Distributed Sequences and Primes

Source: https://erdosproblems.com/997
Status: OPEN

Statement:
Call a sequence x₁, x₂, ... ∈ (0,1) well-distributed if for every ε > 0,
if k is sufficiently large then for all n > 0 and intervals I ⊆ [0,1]:
  |#{n < m ≤ n+k : xₘ ∈ I} - |I| · k| < ε · k

Is it true that for every α, the sequence {αpₙ} is not well-distributed,
where pₙ is the sequence of primes?

Background:
- Well-distributed sequences were introduced by Hlawka and Petersen (1955)
- Erdős proved lacunary sequences {αnₖ} are not well-distributed for almost all α
- Erdős claimed (1964) to have proved existence of α with non-well-distributed {αpₙ}
- He retracted this claim in 1985, saying the proof "perhaps never existed"
- Champagne, Le, Liu, Wooley (2024): Proved ∃ irrational α with non-well-distributed {αpₙ}
- OPEN: Does this hold for ALL α?

References:
- Hlawka [Hl55], "Zur formalen Theorie der Gleichverteilung in kompakten Gruppen"
- Erdős [Er64b], "Problems and results on diophantine approximations"
- Erdős [Er85e], "Some problems and results in number theory"
- Champagne-Le-Liu-Wooley [CLLW24], arXiv:2406.19491
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Primorial
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Set Real

namespace Erdos997

/-
## Part I: Basic Definitions

Fractional parts, intervals, and counting.
-/

/--
**Fractional Part:**
The fractional part {x} of a real number x is x - ⌊x⌋, always in [0, 1).
-/
noncomputable def frac (x : ℝ) : ℝ := x - ⌊x⌋

/--
The fractional part is always in [0, 1).
-/
theorem frac_mem_Ico (x : ℝ) : frac x ∈ Ico 0 1 := by
  simp only [frac, mem_Ico]
  constructor
  · exact sub_floor_div_mul_nonneg x 1
  · have h := sub_floor_div_mul_lt_one x 1
    simp at h
    exact h

/--
**Sequence in Unit Interval:**
A sequence of reals, intended to have values in (0, 1).
-/
def UnitSequence := ℕ → ℝ

/--
**Counting Function:**
Count how many elements of sequence x in the range (n, n+k] fall into interval I.
-/
noncomputable def countInInterval (x : UnitSequence) (n k : ℕ) (I : Set ℝ) : ℕ :=
  Finset.card (Finset.filter (fun m => x m ∈ I) (Finset.Ioc n (n + k)))

/--
**Measure of Interval:**
For a bounded interval in [0, 1], its "measure" (length).
-/
noncomputable def intervalMeasure (a b : ℝ) : ℝ := max 0 (b - a)

/-
## Part II: Well-Distributed Sequences

The notion introduced by Hlawka and Petersen (1955).
-/

/--
**Well-Distributed Sequence:**
A sequence x₁, x₂, ... ∈ (0, 1) is well-distributed if for every ε > 0,
there exists K such that for all k ≥ K, all n ≥ 0, and all intervals I ⊆ [0, 1]:
  |count(x in I over (n, n+k]) - |I| · k| < ε · k

This is a stronger condition than equidistribution, requiring uniformity
across all starting points n.
-/
def WellDistributed (x : UnitSequence) : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ K : ℕ, ∀ k : ℕ, k ≥ K →
      ∀ n : ℕ, ∀ a b : ℝ, 0 ≤ a → b ≤ 1 → a < b →
        |↑(countInInterval x n k (Ioc a b)) - (b - a) * ↑k| < ε * ↑k

/--
**Well-Distributed vs Equidistributed:**
Well-distribution is strictly stronger than equidistribution.
- Equidistribution: limₙ→∞ (1/n) #{m ≤ n : xₘ ∈ I} = |I|
- Well-distribution: uniform version holding for all starting points n

Well-distributed sequences are equidistributed, but not conversely.
-/
axiom well_distributed_implies_equidistributed :
    ∀ x : UnitSequence, WellDistributed x →
      ∀ I : Set ℝ, MeasurableSet I → I ⊆ Icc 0 1 →
        True  -- Simplified: actual equidistribution statement

/-
## Part III: The Prime Sequence

Fractional parts of prime multiples.
-/

/--
**Prime Sequence:**
The function p(n) returning the nth prime (1-indexed: p(1) = 2, p(2) = 3, ...).
-/
noncomputable def primeSequence (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/--
**α-Multiple Sequence of Primes:**
Given α, the sequence {α · pₙ} of fractional parts.
-/
noncomputable def primeMultipleSequence (α : ℝ) : UnitSequence :=
  fun n => frac (α * primeSequence n)

/--
**Values in Unit Interval:**
The prime multiple sequence always has values in [0, 1).
-/
theorem primeMultipleSequence_range (α : ℝ) (n : ℕ) :
    primeMultipleSequence α n ∈ Ico 0 1 :=
  frac_mem_Ico _

/-
## Part IV: Lacunary Sequences

Erdős's result on lacunary sequences.
-/

/--
**Lacunary Sequence:**
A sequence n₁ < n₂ < ... is lacunary if there exists q > 1 such that
nₖ₊₁/nₖ ≥ q for all k. This means the sequence grows at least exponentially.
-/
def Lacunary (s : ℕ → ℕ) : Prop :=
  ∃ q : ℝ, q > 1 ∧ ∀ k : ℕ, (s (k + 1) : ℝ) ≥ q * s k

/--
**Lacunary Sequence Fractional Parts:**
For a lacunary sequence, the α-multiples sequence.
-/
noncomputable def lacunaryMultipleSequence (s : ℕ → ℕ) (α : ℝ) : UnitSequence :=
  fun n => frac (α * s n)

/--
**Erdős's Lacunary Theorem:**
For any lacunary sequence (nₖ), the sequence {α · nₖ} is not well-distributed
for almost all α.

This is a measure-theoretic result: the set of α for which {αnₖ} is
well-distributed has Lebesgue measure zero.
-/
axiom erdos_lacunary_theorem :
    ∀ s : ℕ → ℕ, Lacunary s →
      -- For almost all α, {α · sₖ} is not well-distributed
      True  -- Simplified: actual measure-theoretic statement

/-
## Part V: Primes and Well-Distribution

The main question.
-/

/--
**Erdős's Original (Retracted) Claim (1964):**
Erdős claimed there exists an irrational α such that {αpₙ} is not well-distributed.
He later retracted this claim in 1985.
-/
axiom erdos_1964_retracted_claim :
    -- Erdős claimed but later retracted that he had proved:
    -- ∃ α : ℝ, Irrational α ∧ ¬WellDistributed (primeMultipleSequence α)
    True

/--
**Champagne-Le-Liu-Wooley Theorem (2024):**
There exists an irrational α such that the sequence {αpₙ} is not well-distributed.

This resolved the existence question that Erdős had attempted in 1964.

Reference: arXiv:2406.19491
-/
axiom CLLW_theorem :
    ∃ α : ℝ, Irrational α ∧ ¬WellDistributed (primeMultipleSequence α)

/--
**Erdős Problem #997 (OPEN):**
Is it true that for EVERY α, the sequence {αpₙ} is not well-distributed?

The 2024 result shows this holds for at least one α.
The full conjecture asks whether it holds universally.
-/
def Erdos997Conjecture : Prop :=
  ∀ α : ℝ, ¬WellDistributed (primeMultipleSequence α)

/--
**Rational Case:**
For rational α = p/q, the sequence {αpₙ} has only finitely many values
modulo 1, so cannot be well-distributed in any meaningful sense.
-/
axiom rational_case :
    ∀ p q : ℤ, q ≠ 0 → ¬WellDistributed (primeMultipleSequence (p / q))

/--
**The Hard Case: Irrational α**
For irrational α, the sequence {αpₙ} is equidistributed by Vinogradov.
But well-distribution is stronger, requiring uniformity over all starting points.
-/
axiom vinogradov_equidistribution :
    ∀ α : ℝ, Irrational α →
      -- {αpₙ} is equidistributed mod 1
      True  -- Simplified: actual equidistribution statement

/-
## Part VI: Related Concepts

Discrepancy and distribution theory.
-/

/--
**Discrepancy:**
The discrepancy measures how far a sequence is from being uniformly distributed.
For a sequence x₁, ..., xₙ:
  Dₙ = sup_{I} |#{m ≤ n : xₘ ∈ I}/n - |I||

Well-distribution asks that this discrepancy remains uniformly small
across all starting points.
-/
noncomputable def discrepancy (x : UnitSequence) (N : ℕ) : ℝ :=
  ⨆ (a : ℝ) (b : ℝ) (_ : 0 ≤ a) (_ : b ≤ 1) (_ : a < b),
    |↑(countInInterval x 0 N (Ioc a b)) / ↑N - (b - a)|

/--
**Well-Distribution via Discrepancy:**
A sequence is well-distributed iff the discrepancy starting at any n
goes to 0 uniformly.
-/
axiom well_distributed_iff_discrepancy :
    ∀ x : UnitSequence,
      WellDistributed x ↔
        ∀ ε > 0, ∃ K, ∀ k ≥ K, ∀ n, discrepancy (fun m => x (n + m)) k < ε

/--
**Prime Distribution Irregularity:**
The primes have inherent irregularities (prime gaps, twin primes, etc.)
that may propagate to the sequence {αpₙ} regardless of α.
-/
axiom prime_irregularity :
    -- The irregular distribution of primes affects well-distribution properties
    True

/-
## Part VII: Connections to Diophantine Approximation
-/

/--
**Connection to Diophantine Approximation:**
The well-distribution of {αpₙ} is related to how well α can be
approximated by rationals with prime denominators.
-/
axiom diophantine_connection :
    -- Well-distribution relates to approximation properties of α
    True

/--
**Metric Theory:**
By metric theory of Diophantine approximation, the behavior of {αpₙ}
for "generic" (measure-theoretic typical) α may differ from all α.
-/
axiom metric_theory_perspective :
    -- Metric vs universal statements may give different answers
    True

/-
## Part VIII: Status and Implications
-/

/--
**Current Knowledge (2024):**
1. ∃ irrational α: {αpₙ} not well-distributed [CLLW24]
2. For lacunary sequences: not well-distributed for almost all α [Erdős]
3. Primes are not lacunary (gaps grow, but ratio pₙ₊₁/pₙ → 1)
4. Universal statement for all α: OPEN
-/
theorem current_status :
    -- CLLW proved existence
    (∃ α : ℝ, Irrational α ∧ ¬WellDistributed (primeMultipleSequence α))
    -- but universality is unknown
    := CLLW_theorem

/--
**Why the Problem is Hard:**
- Primes are not lacunary: pₙ₊₁/pₙ → 1 by prime number theorem
- Vinogradov: {αpₙ} IS equidistributed for irrational α
- Well-distribution is strictly stronger than equidistribution
- Depends on subtle properties of prime gaps and α's continued fraction
-/
axiom problem_difficulty :
    -- Primes' growth rate makes lacunary techniques inapplicable
    True

/-
## Part IX: Summary
-/

/--
**Erdős Problem #997 Summary:**

Is it true that for every α, the sequence {αpₙ} is not well-distributed?

**Status:** OPEN

**Known Results:**
- 2024: ∃ irrational α with non-well-distributed {αpₙ} [CLLW24]
- Rational α: trivially not well-distributed
- Lacunary sequences: not well-distributed for almost all α

**Open Questions:**
1. Does the conjecture hold for all irrational α?
2. What is the measure of the set of α for which {αpₙ} is well-distributed?
3. Can the CLLW construction be generalized?
-/
theorem erdos_997_summary :
    -- Existence proved, universality open
    (∃ α : ℝ, Irrational α ∧ ¬WellDistributed (primeMultipleSequence α)) ∧
    -- Full conjecture is still open
    True
    := ⟨CLLW_theorem, trivial⟩

/--
**The Conjecture (OPEN):**
For all α, the sequence {αpₙ} is not well-distributed.
-/
theorem erdos_997_conjecture_statement : Prop := Erdos997Conjecture

end Erdos997
