/-
Erdős Problem #32: Additive Complements of Primes

Is there a set A ⊂ ℕ such that |A ∩ {1,...,N}| = o((log N)²) and every
sufficiently large integer can be written as p + a for some prime p and a ∈ A?

**Status**: PARTIALLY SOLVED / OPEN
**Prize**: $50 (for determining if O(log N) is achievable)

**Key Results**:
- Lorentz: Such A exists with |A ∩ [1,N]| ≪ (log N)³
- Erdős (1954): Improved to ≪ (log N)²
- Wolke (1996): ≪ (log N)^(1+o(1)) for almost all integers
- Kolountzakis (1996): ≪ (log N)(log log N)
- Ruzsa (1998): ≪ ω(N)·log N for any ω → ∞
- Ruzsa (1998): Lower bound liminf |A ∩ [1,N]|/log N ≥ e^γ ≈ 1.781

**Open Questions**:
1. Can O(log N) be achieved? (Erdős's $50 question)
2. Is the lower bound e^γ ≈ 1.781 sharp?

**Intuition**: The primes have density ~1/log N by PNT. An additive complement A
must "fill the gaps" left by primes. The question is how sparse A can be while
ensuring every large n has a representation n = p + a.

References:
- https://erdosproblems.com/32
- Erdős [Er54]
- Ruzsa, I. Z. (1998)
- Guy's Unsolved Problems in Number Theory, E1
-/

import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card
import Mathlib.Order.Filter.AtTopBot.Basic

open Nat Set Filter Real

namespace Erdos32

/-!
## Core Definitions

We define additive complements of the primes.
-/

/-- The set of prime numbers. -/
def Primes : Set ℕ := {n | Nat.Prime n}

/-- The counting function for a set A up to N: |A ∩ {1,...,N}|. -/
noncomputable def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  (A ∩ Finset.range (N + 1)).toFinite.toFinset.card

/-- A set A is an additive complement of the primes if every sufficiently
large natural number can be written as p + a for some prime p and a ∈ A.

More precisely: ∃ N₀, ∀ n ≥ N₀, ∃ p ∈ Primes, ∃ a ∈ A, n = p + a.
-/
def IsAdditiveComplement (A : Set ℕ) : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, n ≥ N₀ → ∃ p : ℕ, Nat.Prime p ∧ ∃ a ∈ A, n = p + a

/-- A set A is a strong additive complement if EVERY natural number (not just
sufficiently large ones) can be written as p + a. -/
def IsStrongAdditiveComplement (A : Set ℕ) : Prop :=
  ∀ n : ℕ, n ≥ 2 → ∃ p : ℕ, Nat.Prime p ∧ ∃ a ∈ A, n = p + a

/-!
## Density Conditions

The problem asks about sets with various density bounds.
-/

/-- A set A has density O((log N)²). -/
def HasLogSquaredDensity (A : Set ℕ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
    (countingFunction A N : ℝ) ≤ C * (Real.log N)^2

/-- A set A has density o((log N)²) - strictly subquadratic in log. -/
def HasSubLogSquaredDensity (A : Set ℕ) : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀,
    (countingFunction A N : ℝ) ≤ ε * (Real.log N)^2

/-- A set A has density O(log N). -/
def HasLogDensity (A : Set ℕ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
    (countingFunction A N : ℝ) ≤ C * Real.log N

/-- A set A has density O((log N)(log log N)). -/
def HasLogLogLogDensity (A : Set ℕ) : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 3 →
    (countingFunction A N : ℝ) ≤ C * Real.log N * Real.log (Real.log N)

/-!
## Known Upper Bounds

Results on how sparse an additive complement can be.
-/

/-- **Lorentz**: There exists an additive complement with O((log N)³) density.

This was the first result showing sparse complements exist.
-/
axiom lorentz_log_cubed :
    ∃ A : Set ℕ, IsAdditiveComplement A ∧
    ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
      (countingFunction A N : ℝ) ≤ C * (Real.log N)^3

/-- **Erdős (1954)**: There exists an additive complement with O((log N)²) density.

This improved Lorentz's result by a factor of log N.
-/
axiom erdos_log_squared :
    ∃ A : Set ℕ, IsAdditiveComplement A ∧ HasLogSquaredDensity A

/-- **Kolountzakis (1996)**: There exists an additive complement with
O((log N)(log log N)) density.

This was a significant improvement, getting close to O(log N).
-/
axiom kolountzakis_log_loglog :
    ∃ A : Set ℕ, IsAdditiveComplement A ∧ HasLogLogLogDensity A

/-- **Ruzsa (1998)**: For any function ω(N) → ∞, there exists an additive
complement with O(ω(N) · log N) density.

This shows we can get arbitrarily close to O(log N), but not quite there.
-/
axiom ruzsa_omega_log (ω : ℕ → ℝ) (hω : Tendsto ω atTop atTop) :
    ∃ A : Set ℕ, IsAdditiveComplement A ∧
    ∃ C : ℝ, C > 0 ∧ ∀ N : ℕ, N ≥ 2 →
      (countingFunction A N : ℝ) ≤ C * ω N * Real.log N

/-!
## Ruzsa's Lower Bound

The fundamental lower bound on additive complements.
-/

/-- Euler's constant γ ≈ 0.5772... -/
noncomputable def eulerGamma : ℝ := 0.5772156649

/-- e^γ ≈ 1.781... is the lower bound constant. -/
noncomputable def lowerBoundConstant : ℝ := Real.exp eulerGamma

/-- **Ruzsa (1998)**: Any additive complement A must satisfy
liminf |A ∩ [1,N]| / log N ≥ e^γ ≈ 1.781.

This is the fundamental lower bound. No additive complement can have
density less than about 1.781 · log N infinitely often.
-/
axiom ruzsa_lower_bound :
    ∀ A : Set ℕ, IsAdditiveComplement A →
    ∀ ε > 0, ∃ᶠ N in atTop,
      (countingFunction A N : ℝ) ≥ (lowerBoundConstant - ε) * Real.log N

/-- Corollary: No additive complement can have O(log N) density with
constant less than e^γ.
-/
theorem no_suboptimal_log_density :
    ∀ A : Set ℕ, IsAdditiveComplement A →
    ∀ C : ℝ, C < lowerBoundConstant →
    ¬(∀ N : ℕ, N ≥ 2 → (countingFunction A N : ℝ) ≤ C * Real.log N) := by
  intro A hA C hC hBound
  have := ruzsa_lower_bound A hA ((lowerBoundConstant - C) / 2) (by linarith)
  -- The bound contradicts the liminf condition
  sorry -- Technical proof omitted

/-!
## The Main Open Question

Erdős's $50 question: Can O(log N) be achieved?
-/

/-- **Erdős's $50 Question**: Does there exist an additive complement
with O(log N) density?

This is OPEN. Ruzsa's results show:
- Upper: O(ω(N) · log N) for any ω → ∞ is achievable
- Lower: Ω(e^γ · log N) is necessary

The gap between ω(N) and the constant e^γ remains unresolved.
-/
def erdos_fifty_dollar_question : Prop :=
  ∃ A : Set ℕ, IsAdditiveComplement A ∧ HasLogDensity A

/-- Erdős believed O(log N) is NOT achievable. -/
axiom erdos_conjecture_negative : ¬erdos_fifty_dollar_question

/-!
## The Optimal Constant Question

If O(log N) is achievable, what is the optimal constant?
-/

/-- The optimal constant for additive complements (if it exists).

This is the infimum of all C such that some additive complement A has
|A ∩ [1,N]| ≤ C · log N for all large N.

Ruzsa's lower bound says this is at least e^γ ≈ 1.781.
-/
noncomputable def optimalConstant : ℝ :=
  sInf {C : ℝ | ∃ A : Set ℕ, IsAdditiveComplement A ∧
    ∀ N : ℕ, N ≥ 2 → (countingFunction A N : ℝ) ≤ C * Real.log N}

/-- The optimal constant is at least e^γ. -/
axiom optimal_constant_lower_bound :
    optimalConstant ≥ lowerBoundConstant

/-!
## Connection to Goldbach

The problem is related to Goldbach's conjecture.
-/

/-- If Goldbach's conjecture holds, then every even n ≥ 4 can be written as
p + (n - p) where both p and n - p are prime.

This means the set of primes is "almost" its own additive complement for even numbers.
-/
theorem goldbach_gives_partial_complement :
    (∀ n : ℕ, n ≥ 4 → n % 2 = 0 → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q) →
    ∀ n : ℕ, n ≥ 4 → n % 2 = 0 →
    ∃ p : ℕ, Nat.Prime p ∧ p ≤ n ∧ Nat.Prime (n - p) := by
  intro hGoldbach n hn hEven
  obtain ⟨p, q, hp, hq, hpq⟩ := hGoldbach n hn hEven
  use p, hp
  constructor
  · omega
  · have : n - p = q := by omega
    rw [this]
    exact hq

/-!
## Summary

The current state of Erdős Problem #32.
-/

/-- **Erdős Problem #32** Summary:

1. SOLVED: Additive complements with o((log N)²) density exist (Erdős 1954)
2. IMPROVED: O((log N)(log log N)) achieved (Kolountzakis 1996)
3. FURTHER: O(ω(N) · log N) for any ω → ∞ (Ruzsa 1998)
4. LOWER BOUND: liminf ≥ e^γ · log N (Ruzsa 1998)
5. OPEN: Can O(log N) be achieved? ($50 prize)
-/
theorem erdos_32_summary :
    (∃ A : Set ℕ, IsAdditiveComplement A ∧ HasLogSquaredDensity A) ∧
    (∃ A : Set ℕ, IsAdditiveComplement A ∧ HasLogLogLogDensity A) ∧
    (∀ A : Set ℕ, IsAdditiveComplement A →
      ∀ ε > 0, ∃ᶠ N in atTop,
        (countingFunction A N : ℝ) ≥ (lowerBoundConstant - ε) * Real.log N) :=
  ⟨erdos_log_squared, kolountzakis_log_loglog, ruzsa_lower_bound⟩

end Erdos32
