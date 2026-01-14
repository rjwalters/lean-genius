/-
  Erdős Problem #3: Arithmetic Progressions in Large Sets

  Source: https://erdosproblems.com/3
  Status: OPEN
  Prize: $5,000

  Statement:
  If A ⊆ ℕ has Σ(1/n : n ∈ A) = ∞, must A contain arbitrarily long
  arithmetic progressions?

  This is equivalent to asking: for all k, is r_k(N) = o(N / log N)?
  where r_k(N) is the maximum size of a subset of {1,...,N} without k-term AP.

  Key Results:
  - Roth (1953): r_3(N) = o(N), first non-trivial bound
  - Szemerédi (1975): r_k(N) = o(N) for all k
  - Gowers (2001): r_k(N) ≪ N / (log log N)^{c_k}
  - Bloom-Sisask (2020): Better bounds for k=3
  - Kelley-Meka (2023): r_3(N) ≪ N / exp((log N)^{1/11})
  - Leng-Sah-Sawhney (2024): r_k(N) ≪ N / exp((log log N)^{c_k})

  The conjecture remains OPEN because current bounds are not strong enough
  to imply r_k(N) = o(N / log N).
-/

import Mathlib

open Set Filter Nat Finset

namespace Erdos3

/-! ## Core Definitions -/

/-- A k-term arithmetic progression starting at a with common difference d -/
def ArithProg (a d k : ℕ) : Finset ℕ :=
  (Finset.range k).map ⟨fun i => a + i * d, fun _ _ h => by omega⟩

/-- A set contains a k-term AP if some (a, d) with d > 0 gives a subset -/
def ContainsAP (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, d > 0 ∧ ↑(ArithProg a d k) ⊆ A

/-- A set contains arbitrarily long APs -/
def ContainsArbitrarilyLongAP (A : Set ℕ) : Prop :=
  ∀ k : ℕ, ContainsAP A k

/-- A set is AP-free of length k (avoids k-term APs) -/
def IsAPFree (A : Set ℕ) (k : ℕ) : Prop :=
  ¬ContainsAP A k

/-- The reciprocal sum of a set -/
noncomputable def reciprocalSum (A : Set ℕ) : ℝ :=
  ∑' (n : A), (1 : ℝ) / n

/-- A set has divergent reciprocal sum -/
def HasDivergentSum (A : Set ℕ) : Prop :=
  ¬Summable (fun n : A => (1 : ℝ) / n)

/-! ## Roth Function r_k(N) -/

/-- r_k(N) = maximum size of subset of {1,...,N} avoiding k-term APs -/
noncomputable def rothNumber (k N : ℕ) : ℕ :=
  Finset.sup
    ((Finset.range (N + 1)).powerset.filter (fun S => IsAPFree (↑S : Set ℕ) k))
    Finset.card

/-- The counting function for A up to N -/
def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (· ∈ A)).card

/-! ## Key Threshold -/

/-- The conjecture is equivalent to: r_k(N) = o(N / log N) for all k -/
def SublogarithmicGrowth (k : ℕ) : Prop :=
  ∀ c : ℝ, c > 0 → ∀ᶠ N in atTop,
    (rothNumber k N : ℝ) < c * N / Real.log N

/-- Erdős Problem #3: Main Conjecture (OPEN) -/
def Erdos3Conjecture : Prop :=
  ∀ A : Set ℕ, HasDivergentSum A → ContainsArbitrarilyLongAP A

/-! ## Historical Results -/

/-- **Roth's Theorem (1953)**: Sets with positive density contain 3-term APs.
    First breakthrough: r_3(N) = o(N). -/
axiom roth_theorem :
  ∀ A : Set ℕ, (∀ M : ℕ, ∃ N > M, (countingFunction A N : ℝ) / N > 0) →
    ContainsAP A 3

/-- **Szemerédi's Theorem (1975)**: r_k(N) = o(N) for all k.
    Sets with positive density contain arbitrarily long APs.
    Won the Abel Prize (2012). -/
axiom szemeredi_theorem :
  ∀ k : ℕ, k ≥ 3 → ∀ε : ℝ, ε > 0 → ∀ᶠ N in atTop,
    (rothNumber k N : ℝ) < ε * N

/-- **Gowers' Bounds (2001)**: r_k(N) ≪ N / (log log N)^{c_k}.
    Won the Fields Medal partly for this work. -/
axiom gowers_bound (k : ℕ) (hk : k ≥ 3) :
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in atTop,
    (rothNumber k N : ℝ) ≤ N / (Real.log (Real.log N))^c

/-- **Kelley-Meka (2023)**: r_3(N) ≪ N / exp((log N)^{1/11}).
    Massive improvement for 3-term APs. -/
axiom kelley_meka_k3 :
  ∀ᶠ N in atTop,
    (rothNumber 3 N : ℝ) ≤ N / Real.exp ((Real.log N)^(1/11 : ℝ))

/-- **Leng-Sah-Sawhney (2024)**: r_k(N) ≪ N / exp((log log N)^{c_k}).
    Current best general bound. -/
axiom leng_sah_sawhney_bound (k : ℕ) (hk : k ≥ 3) :
  ∃ c : ℝ, c > 0 ∧ ∀ᶠ N in atTop,
    (rothNumber k N : ℝ) ≤ N / Real.exp ((Real.log (Real.log N))^c)

/-! ## The Gap -/

/-- **The Critical Gap**: Why the conjecture remains open.
    For Erdős' conjecture, we need r_k(N) = o(N / log N).
    But current bounds only give r_k(N) = o(N / exp((log log N)^c)).
    Since exp((log log N)^c) grows slower than log N, there's a gap. -/

/-- The required bound for the conjecture -/
def RequiredBound (k : ℕ) : Prop :=
  ∀ c : ℝ, c > 0 → ∀ᶠ N in atTop,
    (rothNumber k N : ℝ) ≤ c * N / Real.log N

/-- If r_k(N) = o(N / log N) for all k, then the conjecture holds -/
theorem required_bound_implies_conjecture :
    (∀ k : ℕ, k ≥ 3 → RequiredBound k) → Erdos3Conjecture := by
  intro hbound A hdiv
  intro k
  -- If r_k(N) = o(N / log N), then any set with divergent reciprocal sum
  -- cannot avoid k-APs because its counting function grows too fast
  sorry

/-! ## Equivalent Formulations -/

/-- **Equivalent to Behrend-type bounds**: The conjecture asks whether
    Behrend's construction cannot be improved to achieve N / log N density. -/

/-- Behrend (1946): There exist AP-free sets of size N / exp(c √(log N)) -/
axiom behrend_construction :
  ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, N ≥ 2 →
    ∃ A : Finset ℕ, ↑A ⊆ Finset.range (N + 1) ∧
      IsAPFree (↑A : Set ℕ) 3 ∧
      (A.card : ℝ) ≥ N / Real.exp (c * Real.sqrt (Real.log N))

/-- Elkin (2011): Improved Behrend by logarithmic factor -/
axiom elkin_improvement :
  ∃ c : ℝ, c > 0 ∧ ∀ N : ℕ, N ≥ 2 →
    ∃ A : Finset ℕ, ↑A ⊆ Finset.range (N + 1) ∧
      IsAPFree (↑A : Set ℕ) 3 ∧
      (A.card : ℝ) ≥ c * N * Real.sqrt (Real.log (Real.log N)) /
        Real.exp (4 * Real.sqrt (2 * Real.log N))

/-! ## Green-Tao Connection -/

/-- **Green-Tao Theorem (2008)**: Primes contain arbitrarily long APs.
    Erdős believed solving Problem #3 would lead to this result. -/
axiom green_tao_primes :
  ContainsArbitrarilyLongAP { p : ℕ | Nat.Prime p }

/-- The primes have divergent reciprocal sum (Euler, 1737) -/
axiom euler_prime_sum_diverges :
  HasDivergentSum { p : ℕ | Nat.Prime p }

/-- If Erdős #3 were true, Green-Tao would be a corollary -/
theorem erdos3_implies_green_tao :
    Erdos3Conjecture → ContainsArbitrarilyLongAP { p : ℕ | Nat.Prime p } := by
  intro hconj
  exact hconj { p : ℕ | Nat.Prime p } euler_prime_sum_diverges

/-! ## Small Examples -/

/-- 3-term AP: {a, a+d, a+2d} -/
example : ArithProg 1 2 3 = {1, 3, 5} := by decide

/-- 4-term AP: {a, a+d, a+2d, a+3d} -/
example : ArithProg 2 3 4 = {2, 5, 8, 11} := by decide

/-- The set {1, 2, 4, 5, 10, 11, 13, 14} is 3-AP-free (Roth's example) -/
-- This is a classic construction avoiding 3-term APs

/-! ## Problem Status -/

/-- **Erdős Problem #3: OPEN ($5,000 prize)**

The conjecture that every set with divergent reciprocal sum contains
arbitrarily long arithmetic progressions remains unresolved.

**What we know:**
- Szemerédi (1975): Positive density implies all APs ✓
- Gowers (2001): Improved density bounds
- Kelley-Meka (2023): Near-optimal for k=3
- Leng-Sah-Sawhney (2024): Best general bounds

**What we need:**
- Prove r_k(N) = o(N / log N) for all k, OR
- Find a counterexample: a set with divergent sum avoiding some k-AP

**Difficulty:**
- The current gap between constructions (≈ N/exp(√log N)) and
  required bound (N/log N) seems very hard to close.
- Neither a proof nor counterexample appears within reach.

References:
- Bloom, Sisask (2020): "Breaking the logarithmic barrier"
- Kelley, Meka (2023): "Strong bounds for 3-progressions"
- Leng, Sah, Sawhney (2024): "Improved bounds for Szemerédi's theorem"
-/
theorem erdos_3_open : Erdos3Conjecture ∨ ¬Erdos3Conjecture := by
  exact Classical.em Erdos3Conjecture

end Erdos3
