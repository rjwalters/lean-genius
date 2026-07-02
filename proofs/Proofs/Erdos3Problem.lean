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

/- ## Core Definitions -/

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

/- ## Roth Function r_k(N) -/

/-- r_k(N) = maximum size of subset of {1,...,N} avoiding k-term APs -/
noncomputable def rothNumber (k N : ℕ) : ℕ :=
  Finset.sup
    ((Finset.range (N + 1)).powerset.filter (fun S => IsAPFree (↑S : Set ℕ) k))
    Finset.card

/-- The counting function for A up to N -/
def countingFunction (A : Set ℕ) (N : ℕ) : ℕ :=
  ((Finset.range (N + 1)).filter (· ∈ A)).card

/- ## Key Threshold -/

/-- The conjecture is equivalent to: r_k(N) = o(N / log N) for all k -/
def SublogarithmicGrowth (k : ℕ) : Prop :=
  ∀ c : ℝ, c > 0 → ∀ᶠ N in atTop,
    (rothNumber k N : ℝ) < c * N / Real.log N

/-- Erdős Problem #3: Main Conjecture (OPEN) -/
def Erdos3Conjecture : Prop :=
  ∀ A : Set ℕ, HasDivergentSum A → ContainsArbitrarilyLongAP A

/- ## Historical Results -/

/- ## The Gap -/

/-- **The Critical Gap**: Why the conjecture remains open.
    For Erdős' conjecture, we need r_k(N) = o(N / log N).
    But current bounds only give r_k(N) = o(N / exp((log log N)^c)).
    Since exp((log log N)^c) grows slower than log N, there's a gap. -/

/-- The required bound for the conjecture -/
def RequiredBound (k : ℕ) : Prop :=
  ∀ c : ℝ, c > 0 → ∀ᶠ N in atTop,
    (rothNumber k N : ℝ) ≤ c * N / Real.log N

/-- **Bridge lemma (density from AP-freeness).**
    If `A` avoids `k`-term arithmetic progressions, then its counting function up to
    `N` is bounded by the Roth number `r_k(N)`. This turns the *structural* hypothesis
    "`A` is `k`-AP-free" into a *quantitative* density bound, and is the first honest
    step of any proof of `required_bound_implies_conjecture`.

    Proof: the finite slice `A ∩ {0,…,N}` is itself `k`-AP-free (a `k`-AP inside the
    slice would be a `k`-AP inside `A`), hence it is one of the sets over which
    `rothNumber` takes its supremum, so its cardinality is `≤ r_k(N)`.

    This lemma is fully proved (no `sorry`, no new axiom). -/
theorem countingFunction_le_rothNumber (A : Set ℕ) (k N : ℕ)
    (hA : IsAPFree A k) : countingFunction A N ≤ rothNumber k N := by
  -- The slice coerces into `A`, so any AP it contains is an AP of `A`.
  have hSA : (↑((Finset.range (N + 1)).filter (· ∈ A)) : Set ℕ) ⊆ A := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_filter] at hx
    exact hx.2
  -- The slice is a member of the family `rothNumber` sups over.
  have hmem : ((Finset.range (N + 1)).filter (· ∈ A)) ∈
      ((Finset.range (N + 1)).powerset.filter
        (fun S => IsAPFree (↑S : Set ℕ) k)) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro hAP
    apply hA
    obtain ⟨a, d, hd, hsub⟩ := hAP
    exact ⟨a, d, hd, hsub.trans hSA⟩
  -- Its cardinality is therefore `≤` the supremum, which is `r_k(N)`.
  unfold countingFunction rothNumber
  exact Finset.le_sup hmem

/-- **The analytic gap, made precise.**
    The bound `RequiredBound k` (i.e. `r_k(N) = o(N / log N)`) is *not strong enough*
    to prove `required_bound_implies_conjecture`. Combining the bridge lemma above
    with dyadic (Abel) summation, a `k`-AP-free set `A` satisfies
    `∑_{a ∈ A, a ≤ 2^J} 1/a ≤ ∑_{j} r_k(2^j)·2^{1-j}`. Under `r_k(N) = o(N/log N)`
    the `j`-th term is `o(1/j)`, and `∑ o(1/j)` may still diverge (e.g. the counting
    function `N / (log N · log log N)` is `o(N/log N)` yet has divergent reciprocal
    sum). The genuinely sufficient hypothesis is the stronger
    `r_k(N) = O(N / (log N)^{1+δ})` for some `δ > 0`, which is recorded here as the
    correct threshold for a future proof of the reduction. -/
def StrongRequiredBound (k : ℕ) : Prop :=
  ∃ δ : ℝ, δ > 0 ∧ ∃ C : ℝ, C > 0 ∧ ∀ᶠ N in atTop,
    (rothNumber k N : ℝ) ≤ C * N / (Real.log N) ^ (1 + δ)

/-- If r_k(N) = o(N / log N) for all k, then the conjecture holds.

    OPEN CRUX. See `countingFunction_le_rothNumber` (proved) for the first step and
    `StrongRequiredBound` for why `RequiredBound` alone is insufficient: closing the
    remaining gap requires an analytic (Abel-summation) argument that only goes
    through under a bound of the form `r_k(N) = O(N / (log N)^{1+δ})`. With the
    `RequiredBound` hypothesis exactly as stated the implication is not known to be
    provable. -/
theorem required_bound_implies_conjecture :
    (∀ k : ℕ, k ≥ 3 → RequiredBound k) → Erdos3Conjecture := by
  intro hbound A hdiv
  intro k
  -- If r_k(N) = o(N / log N), then any set with divergent reciprocal sum
  -- cannot avoid k-APs because its counting function grows too fast.
  -- The structural first step (AP-free ⟹ density ≤ r_k(N)) is now the proved lemma
  -- `countingFunction_le_rothNumber`; the remaining step is the analytic summation
  -- gap documented at `StrongRequiredBound`.
  sorry

/- ## Equivalent Formulations -/

/-- **Equivalent to Behrend-type bounds**: The conjecture asks whether
    Behrend's construction cannot be improved to achieve N / log N density. -/

/- ## Green-Tao Connection -/

/-- The primes have divergent reciprocal sum (Euler, 1737) -/
axiom euler_prime_sum_diverges :
  HasDivergentSum { p : ℕ | Nat.Prime p }

/-- If Erdős #3 were true, Green-Tao would be a corollary -/
theorem erdos3_implies_green_tao :
    Erdos3Conjecture → ContainsArbitrarilyLongAP { p : ℕ | Nat.Prime p } := by
  intro hconj
  exact hconj { p : ℕ | Nat.Prime p } euler_prime_sum_diverges

/- ## Small Examples -/

/-- 3-term AP: {a, a+d, a+2d} -/
example : ArithProg 1 2 3 = {1, 3, 5} := by decide

/-- 4-term AP: {a, a+d, a+2d, a+3d} -/
example : ArithProg 2 3 4 = {2, 5, 8, 11} := by decide

/-- The set {1, 2, 4, 5, 10, 11, 13, 14} is 3-AP-free (Roth's example) -/
-- This is a classic construction avoiding 3-term APs

/- ## Problem Status -/

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
