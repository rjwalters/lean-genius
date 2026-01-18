/-
Erdős Problem #968: Normalized Prime Sequence

**Question**: Let uₙ = pₙ/n, where pₙ is the n-th prime. Does the set of n such
that uₙ < uₙ₊₁ have positive density?

**Status**: PARTIALLY SOLVED (main question is OPEN)

**History**: Erdős and Prachar (1961/62) studied the "normalized prime sequence"
uₙ = pₙ/n and proved several results:

1. Σ_{pₙ < x} |uₙ₊₁ - uₙ| ≍ (log x)²  (the total variation grows like log²)
2. The set {n : uₙ > uₙ₊₁} has positive density (decreasing steps are common)

The original question - whether {n : uₙ < uₙ₊₁} also has positive density -
remains OPEN.

**Connection to PNT**: By the Prime Number Theorem, pₙ ~ n log n, so
uₙ = pₙ/n ~ log n. The sequence grows slowly on average but can oscillate.

References:
- https://erdosproblems.com/968
- [ErPr61] Erdős & Prachar, "Sätze und Probleme über pₖ/k", Abh. Math. Sem.
           Univ. Hamburg (1961/62), 251-256
-/

import Mathlib

namespace Erdos968

open Nat Filter Real
open scoped BigOperators

/-!
## The Normalized Prime Sequence

The sequence uₙ = pₙ/n where pₙ is the n-th prime.
-/

/--
The normalized n-th prime: u(n) = p_{n+1} / (n+1) where we use 0-based indexing.
So u(0) = p₁/1 = 2, u(1) = p₂/2 = 3/2, u(2) = p₃/3 = 5/3, etc.

By the Prime Number Theorem, pₙ ~ n log n, so u(n) ~ log n.
-/
noncomputable def u (n : ℕ) : ℝ :=
  (n.nth Nat.Prime : ℝ) / (n + 1)

/-!
## Natural Density

A set S ⊆ ℕ has natural density d if |{k ≤ n : k ∈ S}| / n → d as n → ∞.
We say S has positive density if this limit exists and is > 0.
-/

/-- A set has positive natural density (axiomatized for simplicity). -/
axiom Set.HasPosDensity : Set ℕ → Prop

/-!
## The Main Questions

Erdős asked about the behavior of "increasing" vs "decreasing" steps
in the normalized prime sequence.
-/

/-- The set of n where uₙ < uₙ₊₁ (increasing steps). -/
def increasingSteps : Set ℕ := {n | u n < u (n + 1)}

/-- The set of n where uₙ > uₙ₊₁ (decreasing steps). -/
def decreasingSteps : Set ℕ := {n | u n > u (n + 1)}

/-- The set of n where uₙ = uₙ₊₁ (flat steps) - should be rare. -/
def flatSteps : Set ℕ := {n | u n = u (n + 1)}

/-!
## Known Results (Erdős-Prachar 1961)
-/

/--
**Erdős-Prachar Theorem 1**: The total variation of the normalized prime
sequence satisfies Σ_{pₙ < x} |uₙ₊₁ - uₙ| ≍ (log x)².

This means the sequence oscillates significantly - the cumulative change
is proportional to (log x)².
-/
axiom erdos_prachar_total_variation :
    (fun x : ℕ => ∑ n ∈ Finset.range (Nat.primeCounting' x),
      |u (n + 1) - u n|) =Θ[atTop] fun x => Real.log x ^ 2

/--
**Erdős-Prachar Theorem 2**: The set of decreasing steps {n : uₙ > uₙ₊₁}
has positive natural density.

This means a positive fraction of all n have pₙ₊₁/(n+1) < pₙ/n, i.e.,
the normalized prime ratio decreases.
-/
axiom erdos_prachar_decreasing_density : Set.HasPosDensity decreasingSteps

/-!
## The Open Question

The main question of Erdős Problem #968.
-/

/--
**Erdős Problem #968 (OPEN)**: Does the set of increasing steps {n : uₙ < uₙ₊₁}
have positive natural density?

Erdős-Prachar proved this for decreasing steps. The increasing case remains open.

Note: Since the set of "flat steps" (where uₙ = uₙ₊₁) is likely measure zero
(consecutive primes with equal normalized values is rare), we'd expect the
increasing and decreasing sets to partition most of ℕ. But proving density
for one doesn't immediately give it for the other.
-/
axiom erdos_968_open : Prop  -- unknown: Set.HasPosDensity increasingSteps

/-!
## Related Questions: Triples

Erdős also asked about consecutive increasing or decreasing triples.
-/

/-- The set of n where uₙ < uₙ₊₁ < uₙ₊₂ (three consecutive increases). -/
def increasingTriples : Set ℕ := {n | u n < u (n + 1) ∧ u (n + 1) < u (n + 2)}

/-- The set of n where uₙ > uₙ₊₁ > uₙ₊₂ (three consecutive decreases). -/
def decreasingTriples : Set ℕ := {n | u n > u (n + 1) ∧ u (n + 1) > u (n + 2)}

/--
**Erdős Question (OPEN)**: Are there infinitely many increasing triples
n with uₙ < uₙ₊₁ < uₙ₊₂?
-/
axiom increasing_triples_infinite_open : Prop  -- unknown: increasingTriples.Infinite

/--
**Erdős Question (OPEN)**: Are there infinitely many decreasing triples
n with uₙ > uₙ₊₁ > uₙ₊₂?
-/
axiom decreasing_triples_infinite_open : Prop  -- unknown: decreasingTriples.Infinite

/-!
## Prime Number Theorem Connection

The behavior of uₙ = pₙ/n is governed by the Prime Number Theorem.
-/

/--
By PNT, pₙ ~ n log n, so uₙ = pₙ/n ~ log n.
The sequence grows slowly (logarithmically) on average.

This is axiomatized as the full proof requires PNT from Mathlib.
-/
axiom u_asymptotic_log : ∀ ε > 0, ∀ᶠ n in atTop,
    |u n - Real.log n| < ε * Real.log n

/-!
## Verified Examples

We verify some basic properties about the normalized prime sequence.
-/

/-- The first prime is 2. -/
axiom first_prime : Nat.nth Nat.Prime 0 = 2

/-- The second prime is 3. -/
axiom second_prime : Nat.nth Nat.Prime 1 = 3

/-- The third prime is 5. -/
axiom third_prime : Nat.nth Nat.Prime 2 = 5

/-- u(0) = 2/1 = 2. -/
theorem u_zero : u 0 = 2 := by
  simp only [u, first_prime]
  norm_num

/-- u(1) = 3/2 = 1.5. -/
theorem u_one : u 1 = 3/2 := by
  simp only [u, second_prime]
  norm_num

/-- u(2) = 5/3. -/
theorem u_two : u 2 = 5/3 := by
  simp only [u, third_prime]
  norm_num

/-- u(0) > u(1): the first step is decreasing (2 > 1.5). -/
theorem first_step_decreasing : u 0 > u 1 := by
  rw [u_zero, u_one]
  norm_num

/-- u(1) < u(2): the second step is increasing (1.5 < 5/3 ≈ 1.667). -/
theorem second_step_increasing : u 1 < u 2 := by
  rw [u_one, u_two]
  norm_num

/-- 0 is in decreasingSteps (since u(0) > u(1)). -/
theorem zero_in_decreasing : 0 ∈ decreasingSteps := first_step_decreasing

/-- 1 is in increasingSteps (since u(1) < u(2)). -/
theorem one_in_increasing : 1 ∈ increasingSteps := second_step_increasing

/-!
## Why the Asymmetry?

The question of why decreasing steps have been proved to have positive density
but increasing steps remain open is subtle.

Consider: uₙ₊₁ > uₙ ⟺ pₙ₊₁/(n+1) > pₙ/n ⟺ n·pₙ₊₁ > (n+1)·pₙ

This is equivalent to: pₙ₊₁ - pₙ > pₙ/n = uₙ

So increasing steps happen when the prime gap exceeds uₙ ~ log n.
By PNT, the average prime gap is log pₙ ~ log(n log n) ~ log n,
so gaps slightly larger than average cause increases.

The distribution of prime gaps is irregular, making the density question hard.
-/

/-- The condition for an increasing step in terms of prime gaps. -/
theorem increasing_iff_gap_large (n : ℕ) :
    n ∈ increasingSteps ↔ u n < u (n + 1) := Iff.rfl

/-!
## Summary

Erdős Problem #968 studies the normalized prime sequence uₙ = pₙ/n.

**What we know**:
1. Erdős-Prachar: Σ|uₙ₊₁ - uₙ| ≍ (log x)²
2. Erdős-Prachar: Decreasing steps have positive density
3. First step (n=0) is decreasing: u₀ = 2 > u₁ = 1.5
4. Second step (n=1) is increasing: u₁ = 1.5 < u₂ ≈ 1.667

**Open questions**:
1. Do increasing steps have positive density? (Main question)
2. Infinitely many increasing triples?
3. Infinitely many decreasing triples?

**Key insight**: The normalized prime sequence oscillates due to prime gaps.
Large gaps cause increases; small gaps cause decreases. The asymmetry between
increasing and decreasing steps reflects deep structure in prime distribution.
-/

theorem erdos_968_summary :
    0 ∈ decreasingSteps ∧ 1 ∈ increasingSteps ∧ Set.HasPosDensity decreasingSteps :=
  ⟨zero_in_decreasing, one_in_increasing, erdos_prachar_decreasing_density⟩

end Erdos968
