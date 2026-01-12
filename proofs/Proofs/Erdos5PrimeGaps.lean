/-
  Erdős Problem #5: Prime Gap Limit Points

  Source: https://erdosproblems.com/5
  Status: OPEN

  Statement:
  Let p_n denote the nth prime. For any C ≥ 0, does there exist an infinite
  sequence n_i such that:
    lim_{i→∞} (p_{n_i+1} - p_{n_i}) / log(n_i) = C

  Equivalently: Is the set S of limit points of (p_{n+1} - p_n) / log(n)
  equal to [0, ∞]?

  Known Results:
  - ∞ ∈ S: Westzynthius proved arbitrarily large prime gaps exist
  - 0 ∈ S: Goldston-Pintz-Yildirim established results on small gaps
  - S has positive Lebesgue measure (Erdős, Ricci independently)
  - S contains arbitrarily large finite values (Hildebrand-Maier)
  - [0, c] ⊆ S for some small c > 0 (Pintz)
  - At least 1/3 of [0, ∞) belongs to S (Merikoski)
  - S has bounded gaps (Merikoski)

  What We Can Do:
  1. Define the prime gap function g(n) = p_{n+1} - p_n
  2. Define the normalized gap function g(n) / log(n)
  3. Define the set of limit points S
  4. State the conjecture formally
  5. Prove basic properties about prime gaps

  Tags: number-theory, primes, prime-gaps, erdos-problem
-/

import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

namespace Erdos5

open Filter Real Topology

/-! ## Part I: Basic Definitions -/

/-- The nth prime number (0-indexed: p_0 = 2, p_1 = 3, ...). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The prime gap g(n) = p_{n+1} - p_n. -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- The normalized prime gap: g(n) / log(n).
    This is the quantity whose limit points we study. -/
noncomputable def normalizedGap (n : ℕ) : ℝ :=
  if n = 0 then 0  -- Avoid log(0)
  else (primeGap n : ℝ) / Real.log n

/-! ## Part II: The Set of Limit Points -/

/-- A value C is a limit point of the normalized gap sequence if there exists
    a subsequence converging to C. -/
def IsLimitPoint (C : ℝ) : Prop :=
  ∃ f : ℕ → ℕ, StrictMono f ∧ Tendsto (normalizedGap ∘ f) atTop (nhds C)

/-- The set S of all limit points. -/
def limitPointSet : Set ℝ := {C | IsLimitPoint C}

/-- Infinity is a limit point if normalized gaps are unbounded along some subsequence. -/
def InfinityIsLimitPoint : Prop :=
  ∃ f : ℕ → ℕ, StrictMono f ∧ Tendsto (normalizedGap ∘ f) atTop atTop

/-! ## Part III: The Main Conjecture -/

/-- **Erdős Problem #5** (Main Conjecture)

    Every non-negative real number is a limit point of the normalized prime gaps.
    Together with ∞ being a limit point, this says S = [0, ∞]. -/
def erdos_5 : Prop :=
  (∀ C : ℝ, 0 ≤ C → IsLimitPoint C) ∧ InfinityIsLimitPoint

/-! ## Part IV: Known Results -/

/-- **Westzynthius (1931)**: Prime gaps can be arbitrarily large.
    Equivalently, ∞ is a limit point of normalized gaps.

    More precisely: lim sup (p_{n+1} - p_n) / log(p_n) = ∞ -/
axiom westzynthius_large_gaps : InfinityIsLimitPoint

/-- **Goldston-Pintz-Yildirim (2005)**: There are infinitely many prime gaps
    smaller than the average.

    This implies 0 is a limit point of normalized gaps. -/
axiom goldston_pintz_yildirim_small_gaps : IsLimitPoint 0

/-- **Erdős-Ricci**: The set S has positive Lebesgue measure. -/
axiom erdos_ricci_positive_measure : ∃ ε : ℝ, ε > 0 ∧
  -- Informal: μ(S) > ε where μ is Lebesgue measure
  True

/-- **Merikoski (2020s)**: At least 1/3 of [0, ∞) belongs to S.
    Also: S has bounded gaps (no "large holes"). -/
axiom merikoski_density : ∃ density : ℝ, density ≥ 1/3 ∧
  -- Informal: μ(S ∩ [0, M]) / M ≥ density as M → ∞
  True

/-! ## Part V: Basic Properties -/

/-- The first few primes. -/
theorem nthPrime_zero : nthPrime 0 = 2 := by
  unfold nthPrime
  exact Nat.nth_prime_zero_eq_two

theorem nthPrime_one : nthPrime 1 = 3 := by
  unfold nthPrime
  exact Nat.nth_prime_one_eq_three

theorem nthPrime_two : nthPrime 2 = 5 := by
  unfold nthPrime
  exact Nat.nth_prime_two_eq_five

/-- Prime gaps are always positive (there's always a next prime). -/
theorem primeGap_pos (n : ℕ) : 0 < primeGap n := by
  unfold primeGap nthPrime
  -- p_{n+1} > p_n since primes are strictly increasing
  have h : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) := by
    exact Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self n)
  omega

/-- The first prime gap: p_1 - p_0 = 3 - 2 = 1. -/
theorem primeGap_zero : primeGap 0 = 1 := by
  unfold primeGap nthPrime
  simp [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three]

/-- The second prime gap: p_2 - p_1 = 5 - 3 = 2. -/
theorem primeGap_one : primeGap 1 = 2 := by
  unfold primeGap nthPrime
  simp [Nat.nth_prime_one_eq_three, Nat.nth_prime_two_eq_five]

/-- The nth prime is at least n + 2. -/
theorem nthPrime_ge (n : ℕ) : nthPrime n ≥ n + 2 := by
  unfold nthPrime
  -- The nth prime is at least n + 2 (since 2 is the 0th prime)
  sorry

/-- Primes grow at least linearly. -/
theorem nthPrime_strictMono : StrictMono nthPrime := by
  intro a b hab
  unfold nthPrime
  exact Nat.nth_strictMono Nat.infinite_setOf_prime hab

/-! ## Part VI: Gap Distribution -/

/-- The average gap near n is approximately log(p_n) by the prime number theorem.
    We normalize by log(n) which is asymptotically equivalent. -/
noncomputable def averageGap (n : ℕ) : ℝ := Real.log (nthPrime n)

/-- Cramér's conjecture (1936): The largest gap near n is O((log p_n)²).
    This is stronger than what's needed for Erdős #5 but provides context. -/
def cramer_conjecture : Prop :=
  ∃ C : ℝ, C > 0 ∧ ∀ n : ℕ, (primeGap n : ℝ) ≤ C * (Real.log (nthPrime n))^2

/-! ## Part VII: Connections -/

/-- The twin prime conjecture would imply 0 is a limit point (with specific
    subsequence of twin prime locations). -/
theorem twin_prime_implies_zero_limit (h : ∃ᶠ n in atTop, primeGap n = 2) :
    IsLimitPoint 0 := by
  -- If there are infinitely many twin primes, the gaps of 2 divided by
  -- log(n) → 0 as n → ∞
  sorry

/-- Zhang's theorem (2013): There are infinitely many gaps ≤ 70,000,000.
    This was later improved to gaps ≤ 246 by the Polymath project. -/
axiom zhang_bounded_gaps : ∃ H : ℕ, ∃ᶠ n in atTop, primeGap n ≤ H

/-- Zhang's theorem implies 0 is a limit point. -/
theorem zhang_implies_zero_limit : IsLimitPoint 0 := by
  -- Bounded gaps / log(n) → 0 as n → ∞
  sorry

#check erdos_5
#check limitPointSet
#check IsLimitPoint

end Erdos5
