/-
Erdős Problem #1000: Diophantine Approximation and Generalized Totients

Let A = {n₁ < n₂ < ⋯} be an infinite sequence of positive integers.
Define φ_A(k) as the count of 1 ≤ m ≤ n_k such that the fraction m/n_k
in lowest form has denominator different from all n_j where j < k.

**Question**: Does there exist a sequence A such that
  lim_{N→∞} (1/N) Σ_{k≤N} φ_A(k)/n_k = 0?

**Status**: SOLVED
**Answer**: YES (Haight) - contrary to Erdős' expectation

**History**:
- Cassels (1950): Introduced φ_A, proved liminf can equal 0
- Erdős (1964): Proved limit of φ_A(k)/n_k cannot be 0
- Erdős (1964): If liminf φ_A(k)/n_k = 0 then limsup = 1
- Haight: Proved such a sequence exists, resolving the problem

Reference: https://erdosproblems.com/1000
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Basic
import Mathlib.Data.Real.Basic

open Nat Set Filter

namespace Erdos1000

/-!
## The Generalized Totient Function φ_A

Given a strictly increasing sequence A = {n₁ < n₂ < ⋯} of positive integers,
we define φ_A(k) to count integers m with a specific property related to
reduced fractions and previous sequence elements.
-/

/--
A strictly increasing sequence of positive integers.
Represents A = {n₁ < n₂ < ⋯}.
-/
structure IncreasingSeq where
  seq : ℕ → ℕ
  pos : ∀ k, 0 < seq k
  strict_mono : StrictMono seq

/--
For a fraction m/n in lowest form, the reduced denominator is n/gcd(m,n).
Given m and n, this computes the denominator when m/n is reduced.
-/
def reducedDenom (m n : ℕ) : ℕ := n / Nat.gcd m n

/--
The generalized totient φ_A(k) counts integers 1 ≤ m ≤ n_k such that
when m/n_k is written in lowest form, the denominator is not equal
to any n_j for j < k.

Equivalently: n_k / gcd(m, n_k) ≠ n_j for all 1 ≤ j < k.
-/
def phiA (A : IncreasingSeq) (k : ℕ) : ℕ :=
  (Finset.filter (fun m =>
    m ≥ 1 ∧ ∀ j < k, reducedDenom m (A.seq k) ≠ A.seq j
  ) (Finset.range (A.seq k + 1))).card

/-!
## Basic Properties of φ_A

The generalized totient satisfies φ_A(k) ≥ φ(n_k) always,
with equality when A = ℕ (the natural numbers).
-/

/--
φ_A(k) is always at least φ(n_k), the Euler totient.
This is because any m coprime to n_k has reduced denominator n_k,
which cannot equal any previous n_j (since the sequence is strictly increasing).
-/
theorem phiA_ge_totient (A : IncreasingSeq) (k : ℕ) (hk : k ≥ 1) :
    φ (A.seq k) ≤ phiA A k := by
  sorry

/--
The natural numbers as an increasing sequence.
-/
def naturalSeq : IncreasingSeq where
  seq := fun n => n + 1
  pos := fun k => Nat.succ_pos k
  strict_mono := fun _ _ h => Nat.add_lt_add_right h 1

/--
When A = ℕ, we have φ_A(k) = φ(k) for all k.
This is the baseline case.
-/
theorem phiA_naturals_eq_totient (k : ℕ) (hk : k ≥ 1) :
    phiA naturalSeq k = φ (naturalSeq.seq k) := by
  sorry

/-!
## The Average Density

The main object of study is the Cesàro average of φ_A(k)/n_k.
-/

/--
The density ratio for a single term: φ_A(k) / n_k.
-/
noncomputable def densityRatio (A : IncreasingSeq) (k : ℕ) : ℝ :=
  (phiA A k : ℝ) / (A.seq k : ℝ)

/--
The Cesàro average of the density ratios up to N.
-/
noncomputable def cesaroAverage (A : IncreasingSeq) (N : ℕ) : ℝ :=
  if N = 0 then 0
  else (1 / N : ℝ) * (Finset.range N).sum (fun k => densityRatio A (k + 1))

/-!
## Cassels' Result (1950)

Cassels introduced the study of φ_A and proved that the liminf
of the Cesàro average can be 0 for appropriate sequences.

This connects to Diophantine approximation: the divergence of
Σ f(n_k)/k implies, for almost all α, that |α - m_k/n_k| < f(n_k)/n_k²
for infinitely many k.
-/

/--
Cassels (1950): There exist sequences A where the liminf of
the Cesàro average equals 0.
-/
axiom cassels_liminf_zero :
    ∃ A : IncreasingSeq,
      Filter.liminf (fun N => cesaroAverage A N) atTop = 0

/-!
## Erdős' Results (1964)

Erdős proved two key results about the behavior of φ_A(k)/n_k:

1. The limit of individual terms φ_A(k)/n_k cannot be 0
2. If liminf φ_A(k)/n_k = 0, then limsup φ_A(k)/n_k = 1
-/

/--
Erdős (1964): For any sequence A, the limit of φ_A(k)/n_k as k→∞
cannot be 0.
-/
axiom erdos_no_zero_limit (A : IncreasingSeq) :
    ¬ Filter.Tendsto (densityRatio A) atTop (nhds 0)

/--
Erdős (1964): If liminf φ_A(k)/n_k = 0, then limsup φ_A(k)/n_k = 1.

The proof uses the following argument:
- If liminf = 0, then for any ε > 0, there are arbitrarily large k
  with φ(n_k) < ε · n_k
- This means there are arbitrarily large primes p dividing some n_i
- If n_k is the first element divisible by p, then every m ≤ n_k
  not divisible by p contributes to φ_A(k)
- So φ_A(k)/n_k ≥ 1 - 1/p, which approaches 1 as p→∞
-/
axiom erdos_liminf_limsup (A : IncreasingSeq) :
    Filter.liminf (densityRatio A) atTop = 0 →
    Filter.limsup (densityRatio A) atTop = 1

/-!
## The Main Question

Erdős believed that no sequence A could have the Cesàro average
converge to 0. Haight proved him wrong.
-/

/--
A sequence A has vanishing average if the Cesàro average
of φ_A(k)/n_k tends to 0.
-/
def hasVanishingAverage (A : IncreasingSeq) : Prop :=
  Filter.Tendsto (cesaroAverage A) atTop (nhds 0)

/--
The main question (Erdős): Does there exist a sequence A
with vanishing average?

Erdős conjectured NO. He was wrong.
-/
def erdos_1000_question : Prop :=
  ∃ A : IncreasingSeq, hasVanishingAverage A

/-!
## Haight's Resolution

Haight proved that such a sequence does exist, contrary to
Erdős' expectation. This resolved Problem #1000.
-/

/--
**Haight's Theorem**: There exists a sequence A such that the
Cesàro average of φ_A(k)/n_k converges to 0.

This answered Erdős' question in the affirmative and resolved
Problem #1000.
-/
axiom haight_theorem : erdos_1000_question

/--
Erdős Problem #1000 is SOLVED.
The answer is YES - such sequences exist.
-/
theorem erdos_1000_solved : erdos_1000_question := haight_theorem

/-!
## Connection to Metric Diophantine Approximation

Cassels showed that the property
  liminf (1/N) Σ_{k≤N} φ_A(k)/n_k > 0
is equivalent to a fundamental divergence condition in metric theory:

The divergence of Σ f(n_k)/k implies, for almost all real α,
infinitely many approximations |α - m/n_k| < f(n_k)/n_k².

This connects Problem #1000 to the Khinchin-Groshev theorem
and the general theory of Diophantine approximation.
-/

/--
The connection between φ_A and metric Diophantine approximation.
This characterization is due to Cassels (1950).
-/
def cassels_characterization (A : IncreasingSeq) : Prop :=
  Filter.liminf (cesaroAverage A) atTop > 0 ↔
  -- The divergence condition for Diophantine approximation holds
  True  -- Placeholder for the full statement

/-!
## Observations and Corollaries

Haight's result shows that one can construct sequences where the
"new denominators" become increasingly rare on average.

Combined with Erdős' liminf/limsup result, this means:
- The individual terms φ_A(k)/n_k oscillate between 0 and 1
- But their average still tends to 0
-/

/--
For Haight's sequence, densityRatio oscillates despite vanishing average.
-/
theorem haight_oscillation :
    ∃ A : IncreasingSeq,
      hasVanishingAverage A ∧
      Filter.liminf (densityRatio A) atTop = 0 ∧
      Filter.limsup (densityRatio A) atTop = 1 := by
  obtain ⟨A, hA⟩ := haight_theorem
  refine ⟨A, hA, ?_, ?_⟩
  · -- The average tending to 0 implies liminf of terms is 0
    sorry
  · -- By Erdős' result, limsup must equal 1
    sorry

/-!
## Summary

This file formalizes Erdős Problem #1000 on generalized totient functions
and Diophantine approximation.

**The Question**: For infinite sequence A = {n₁ < n₂ < ⋯}, can
  lim (1/N) Σ φ_A(k)/n_k = 0?

**The Answer**: YES (Haight), contrary to Erdős' expectation.

**Key Results**:
- Cassels (1950): liminf can be 0
- Erdős (1964): individual limit cannot be 0
- Erdős (1964): liminf = 0 implies limsup = 1
- Haight: Cesàro average can converge to 0

**Connection**: The problem relates to metric Diophantine approximation
and the Khinchin-Groshev theory of rational approximations.
-/

end Erdos1000
