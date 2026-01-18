/-
  Erdős Problem #859: Density of Divisor Sum Representations

  Source: https://erdosproblems.com/859
  Status: PARTIALLY SOLVED (bounds known, asymptotics open)

  Statement:
  Let t ≥ 1 and let dₜ be the density of the set of integers n ∈ ℕ for which
  t can be represented as the sum of distinct divisors of n.

  Do there exist constants c₁, c₂ > 0 such that
      dₜ ~ c₁ / (log t)^c₂
  as t → ∞?

  Known Results (Erdős 1970):
  - The density dₜ always exists
  - There exist constants c₃, c₄ > 0 such that
      1/(log t)^c₃ < dₜ < 1/(log t)^c₄

  The open question asks whether dₜ has a precise asymptotic form.

  Examples:
  - t = 0: Every n works (empty sum), so d₀ = 1
  - t = 1: Need 1 | n, which is all n, so d₁ = 1
  - t = 2: Need 2 | n, so d₂ = 1/2
  - t = 3: Need 1 + 2 | n or 3 | n, which is n ≡ 0 (mod 3) or n ≡ 0 (mod 2)

  References:
  [Er70] Erdős, "Some extremal problems in combinatorial number theory" (1970)

  Tags: number-theory, divisors, density, asymptotics
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

namespace Erdos859

open Nat Finset Filter Asymptotics Real

/-! ## Part I: Divisor Sum Sets -/

/-- DivisorSumSet t is the set of natural numbers n such that t can be
    represented as a sum of distinct divisors of n.

    For example, if n = 6 with divisors {1, 2, 3, 6}:
    - t = 0: empty sum ✓
    - t = 1: {1} ✓
    - t = 3: {1, 2} or {3} ✓
    - t = 6: {1, 2, 3} or {6} ✓
    - t = 12: {1, 2, 3, 6} ✓
    - t = 7: {1, 6} ✓ -/
def DivisorSumSet (t : ℕ) : Set ℕ :=
  {n : ℕ | ∃ s ⊆ Nat.divisors n, t = ∑ i in s, i}

/-- Alternative characterization: n ∈ DivisorSumSet t iff some subset
    of divisors of n sums to t. -/
theorem mem_divisorSumSet_iff (t n : ℕ) :
    n ∈ DivisorSumSet t ↔ ∃ s ⊆ Nat.divisors n, t = ∑ i in s, i := by
  rfl

/-! ## Part II: Natural Density -/

/-- The counting function: how many n ≤ N are in DivisorSumSet t? -/
noncomputable def countingFunction (t N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (· ∈ DivisorSumSet t)).card

/-- A set S ⊆ ℕ has natural density d if #{n ≤ N : n ∈ S} / N → d. -/
def HasNaturalDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N => (((Finset.range (N + 1)).filter (· ∈ S)).card : ℝ) / N)
    atTop (𝓝 d)

/-- A set has positive density if its density exists and is positive. -/
def HasPositiveDensity (S : Set ℕ) : Prop :=
  ∃ d : ℝ, d > 0 ∧ HasNaturalDensity S d

/-! ## Part III: Basic Examples -/

/-- t = 0: The empty sum works for every n, so DivisorSumSet 0 = ℕ.
    Thus d₀ = 1. -/
theorem divisorSumSet_zero : DivisorSumSet 0 = Set.univ := by
  ext n
  simp [DivisorSumSet]
  use ∅
  simp

/-- Corollary: The density of DivisorSumSet 0 is 1. -/
theorem density_zero : HasNaturalDensity (DivisorSumSet 0) 1 := by
  rw [divisorSumSet_zero]
  sorry  -- Density of ℕ is 1

/-- t = 1: We need 1 to be a divisor of n (always true for n ≥ 1).
    So DivisorSumSet 1 = ℕ⁺. -/
theorem divisorSumSet_one : ∀ n : ℕ, n > 0 → n ∈ DivisorSumSet 1 := by
  intro n hn
  use {1}
  constructor
  · intro x hx
    simp at hx
    rw [hx]
    exact Nat.one_mem_divisors.mpr (Nat.one_le_iff_ne_zero.mp hn)
  · simp

/-- t = 2: We need 2 to be a divisor (2 | n) or 1 + ? = 2 for divisors.
    The only way is 2 | n. So d₂ = 1/2. -/
theorem mem_divisorSumSet_two (n : ℕ) (hn : n > 0) :
    n ∈ DivisorSumSet 2 ↔ 2 ∣ n := by
  sorry

/-! ## Part IV: Erdős's Bounds (1970) -/

/-- **Erdős (1970)**: The density dₜ exists for all t.

    This is nontrivial: not all sets have natural density.
    The proof uses multiplicative structure of divisor sums. -/
axiom erdos_density_exists (t : ℕ) :
    ∃ d : ℝ, HasNaturalDensity (DivisorSumSet t) d

/-- **Erdős (1970)**: The density is always positive.

    Intuition: For any t, there are infinitely many n with t | σ(n)
    where σ(n) is the sum of all divisors. Finding n where t is a
    subset sum is related but requires more care. -/
axiom erdos_density_positive (t : ℕ) (ht : t > 0) :
    HasPositiveDensity (DivisorSumSet t)

/-- **Erdős (1970)**: Upper and lower bounds of the same form.

    There exist c₃, c₄ > 0 such that for large t:
        1/(log t)^c₃ < dₜ < 1/(log t)^c₄

    This shows dₜ decays polynomially in log t. -/
axiom erdos_bounds :
    ∃ c₃ c₄ : ℝ, c₃ > 0 ∧ c₄ > 0 ∧
      ∀ᶠ t : ℕ in atTop, ∀ dₜ : ℝ, HasNaturalDensity (DivisorSumSet t) dₜ →
        1 / (log t)^c₃ < dₜ ∧ dₜ < 1 / (log t)^c₄

/-! ## Part V: The Open Question -/

/-- **Erdős Problem #859** (Open):

    Do there exist constants c₁, c₂ > 0 such that
        dₜ ~ c₁ / (log t)^c₂
    as t → ∞?

    This asks for a precise asymptotic, not just bounds. -/
def ErdosProblem859 : Prop :=
  ∃ c₁ c₂ : ℝ, c₁ > 0 ∧ c₂ > 0 ∧
    ∃ d : ℕ → ℝ, (∀ t > 0, HasNaturalDensity (DivisorSumSet t) (d t)) ∧
      (fun t : ℕ => d t) ~[atTop] (fun t => c₁ / (log t)^c₂)

/-- The status: OPEN. We don't know if precise asymptotics exist. -/
axiom erdos_859_open : True  -- Placeholder for open status

/-! ## Part VI: The Divisor Function -/

/-- The sum of divisors σ(n) = Σ_{d|n} d. -/
noncomputable def sigma (n : ℕ) : ℕ :=
  (Nat.divisors n).sum id

/-- The number of divisors τ(n) = #{d : d | n}. -/
def tau (n : ℕ) : ℕ :=
  (Nat.divisors n).card

/-- For n with k divisors, there are 2^k possible subset sums.
    So DivisorSumSet t gets contributions from n with many divisors. -/
theorem subset_sum_count (n : ℕ) (hn : n > 0) :
    (Nat.divisors n).powerset.card = 2^(tau n) := by
  simp [tau, Finset.card_powerset]

/-! ## Part VII: Multiplicative Structure -/

/-- If gcd(m, n) = 1, then divisors(mn) = divisors(m) × divisors(n).
    This multiplicative structure helps analyze DivisorSumSet. -/
theorem divisors_mul_coprime {m n : ℕ} (hmn : Nat.Coprime m n) (hm : m > 0) (hn : n > 0) :
    (Nat.divisors (m * n)).card = (Nat.divisors m).card * (Nat.divisors n).card := by
  sorry

/-- Key observation: If n = p₁^a₁ · ... · pₖ^aₖ, then subset sums of
    divisors can be analyzed by considering each prime power separately. -/
theorem primePower_divisors (p : ℕ) (hp : p.Prime) (a : ℕ) :
    Nat.divisors (p^a) = (Finset.range (a + 1)).map ⟨fun i => p^i, fun _ _ => by
      intro h; exact Nat.pow_right_injective hp.two_le h⟩ := by
  sorry

/-! ## Part VIII: Density Comparisons -/

/-- For large t, dₜ is small. This is because most n have σ(n) < t,
    so they can't possibly represent t as a subset sum. -/
theorem density_decreasing :
    ∀ᶠ t : ℕ in atTop, ∀ dₜ : ℝ, HasNaturalDensity (DivisorSumSet t) dₜ →
      dₜ < 1 := by
  sorry

/-- Comparison: d₂ₜ ≤ dₜ for all t.
    If we can represent 2t, we can also represent t (take a smaller subset). -/
theorem density_comparison (t : ℕ) (ht : t > 0) :
    ∀ d₂ₜ dₜ : ℝ, HasNaturalDensity (DivisorSumSet (2 * t)) d₂ₜ →
      HasNaturalDensity (DivisorSumSet t) dₜ →
        d₂ₜ ≤ dₜ := by
  sorry

/-! ## Part IX: Connection to Practical Numbers -/

/-- A practical number is n such that every k ≤ σ(n) can be represented
    as a sum of distinct divisors of n. -/
def IsPractical (n : ℕ) : Prop :=
  ∀ k : ℕ, k ≤ sigma n → n ∈ DivisorSumSet k

/-- Examples of practical numbers: 1, 2, 4, 6, 8, 12, 16, 18, 20, 24, ... -/
theorem practical_examples :
    IsPractical 1 ∧ IsPractical 2 ∧ IsPractical 6 ∧ IsPractical 12 := by
  sorry

/-- Practical numbers have positive density (Margenstern 1991).
    This relates to our problem since practical n contribute to many dₜ. -/
axiom practical_density_positive :
    HasPositiveDensity {n : ℕ | IsPractical n}

/-! ## Part X: Subset Sum Problem -/

/-- The subset sum problem: given a set S and target t, does some
    subset of S sum to t? This is NP-complete in general, but
    for divisor sets, special structure helps. -/
def SubsetSumExists (S : Finset ℕ) (t : ℕ) : Prop :=
  ∃ s ⊆ S, ∑ i in s, i = t

/-- n ∈ DivisorSumSet t iff SubsetSumExists (divisors n) t. -/
theorem divisorSumSet_subsetSum (n t : ℕ) (hn : n > 0) :
    n ∈ DivisorSumSet t ↔ SubsetSumExists (Nat.divisors n) t := by
  simp [DivisorSumSet, SubsetSumExists]

/-! ## Part XI: Growth of σ(n) -/

/-- Average order of σ(n): Σ_{n≤N} σ(n) ~ (π²/12) N². -/
axiom sigma_average_order :
    Tendsto (fun N => (∑ n in Finset.range (N + 1), sigma n : ℝ) / N^2)
      atTop (𝓝 (Real.pi^2 / 12))

/-- For "most" n, σ(n) ≈ n · (some logarithmic factor).
    This bounds how many n can contribute to DivisorSumSet t for large t. -/
axiom sigma_typical_size :
    ∀ᶠ n : ℕ in atTop, sigma n < n * (log n)^2

/-! ## Part XII: Summary -/

/-- Summary of Erdős Problem #859:

    **Status**: PARTIALLY SOLVED / OPEN

    **Known Results (Erdős 1970)**:
    - Density dₜ exists for all t
    - dₜ > 0 for all t > 0
    - 1/(log t)^c₃ < dₜ < 1/(log t)^c₄ for some c₃, c₄ > 0

    **Open Question**:
    - Is dₜ ~ c₁/(log t)^c₂ for some c₁, c₂ > 0?

    **Key Concepts**:
    - DivisorSumSet t: integers n where t is a subset sum of divisors
    - Natural density: limiting proportion of integers in a set
    - Practical numbers: n where ALL k ≤ σ(n) are representable -/
theorem erdos_859_summary :
    (∀ t, ∃ d, HasNaturalDensity (DivisorSumSet t) d) ∧
    (∀ t > 0, HasPositiveDensity (DivisorSumSet t)) ∧
    (∃ c₃ c₄ : ℝ, c₃ > 0 ∧ c₄ > 0 ∧
      ∀ᶠ t : ℕ in atTop, ∀ dₜ, HasNaturalDensity (DivisorSumSet t) dₜ →
        1/(log t)^c₃ < dₜ ∧ dₜ < 1/(log t)^c₄) := by
  refine ⟨erdos_density_exists, ?_, erdos_bounds⟩
  intro t ht
  exact erdos_density_positive t ht

end Erdos859

/-!
## Summary

This file formalizes Erdős Problem #859 on the density of divisor sum
representations.

**Status**: PARTIALLY SOLVED (bounds known) / OPEN (precise asymptotics)

**The Problem**: For which n can t be written as a sum of distinct
divisors of n? What is the density dₜ of such n, and does it have
a precise asymptotic form c₁/(log t)^c₂?

**What we formalize**:
1. DivisorSumSet t: the set of n where t is a divisor subset sum
2. Natural density definition
3. Basic examples (t = 0, 1, 2)
4. Erdős's bounds from 1970
5. The open question about precise asymptotics
6. Connection to practical numbers
7. Subset sum perspective

**Key insight**: The density dₜ decays like a power of log t, but
the precise power and coefficient are unknown. The problem connects
divisibility theory with combinatorics (subset sums) and density.

**Historical Note**: This problem is part of Erdős's extensive work
on the structure of divisors. The 1970 paper established the basic
bounds, but the precise asymptotics remain elusive.
-/
