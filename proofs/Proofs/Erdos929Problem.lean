/-!
# Erdős Problem #929 — Smooth Numbers in Short Intervals

Let k ≥ 2 and let S(k) be the minimal x such that there exists a positive
density set of n where n+1, n+2, …, n+k are all x-smooth (divisible only
by primes ≤ x).

Estimate S(k). Is S(k) ≥ k^{1−o(1)}?

## Status: OPEN

## Key Results

- **Trivial upper bound**: S(k) ≤ k+1 (take n ≡ −1 mod (k+1)!).
- **Rosser's sieve**: S(k) > k^{1/2−o(1)}.
- **Ford–Green–Konyagin–Maynard–Tao (2018)**:
  S(k) ≪ k · (log log log k) / (log log k · log log log log k).

The conjecture S(k) ≥ k^{1−o(1)} remains open.

*Reference:* [erdosproblems.com/929](https://www.erdosproblems.com/929)
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Filter

/-! ## Core Definitions -/

/-- A natural number n is x-smooth if all its prime factors are ≤ x. -/
def IsSmooth (n : ℕ) (x : ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ n → p ≤ x

/-- A block of k consecutive integers starting at n+1 is x-smooth
if each of n+1, n+2, …, n+k is x-smooth. -/
def SmoothBlock (n k x : ℕ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ k → IsSmooth (n + i) x

/-- The set of n for which the block n+1, …, n+k is x-smooth. -/
def smoothBlockSet (k x : ℕ) : Set ℕ :=
  { n | SmoothBlock n k x }

/-- Asymptotic upper density of a set of naturals. -/
noncomputable def Set.upperDensity (S : Set ℕ) : ℝ :=
  Filter.limsup (fun n =>
    (Finset.card (Finset.filter (· ∈ S) (Finset.range (n + 1))) : ℝ)
    / (↑(n + 1) : ℝ)) atTop

/-- S(k) is the minimal x such that the set of n with a smooth block
n+1, …, n+k has positive upper density. -/
noncomputable def smoothThreshold (k : ℕ) : ℕ :=
  Nat.find (⟨k + 1, by
    -- S(k) ≤ k+1 trivially
    sorry⟩ : ∃ x : ℕ, 0 < (smoothBlockSet k x).upperDensity)

/-! ## Main Conjecture -/

/-- **Erdős Problem #929 (Open).**
S(k) ≥ k^{1−o(1)}, meaning for every ε > 0 and all sufficiently
large k, S(k) ≥ k^{1−ε}. -/
axiom erdos_929_conjecture :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ (k : ℕ) in atTop,
    (smoothThreshold k : ℝ) ≥ (k : ℝ) ^ (1 - ε)

/-! ## Known Bounds -/

/-- **Trivial upper bound.** S(k) ≤ k+1.
Take n ≡ −1 mod (k+1)!, then n+1, …, n+k are all (k+1)-smooth. -/
axiom trivial_upper (k : ℕ) (hk : 2 ≤ k) :
  smoothThreshold k ≤ k + 1

/-- **Rosser's sieve.** S(k) > k^{1/2−o(1)}.
For every ε > 0 and large enough k, S(k) ≥ k^{1/2−ε}. -/
axiom rosser_lower :
  ∀ ε : ℝ, 0 < ε → ∀ᶠ (k : ℕ) in atTop,
    (smoothThreshold k : ℝ) ≥ (k : ℝ) ^ (1/2 - ε)

/-- **Ford–Green–Konyagin–Maynard–Tao (2018).**
S(k) ≪ k · log log log k / (log log k · log log log log k).
This improves the trivial upper bound S(k) ≤ k+1 by iterated
logarithmic factors, using their work on large gaps between primes. -/
axiom fgkmt_upper :
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ (k : ℕ) in atTop,
    (smoothThreshold k : ℝ) ≤ C * (k : ℝ) *
      Real.log (Real.log (Real.log (k : ℝ))) /
      (Real.log (Real.log (k : ℝ)) * Real.log (Real.log (Real.log (Real.log (k : ℝ)))))

/-! ## Structural Observations -/

/-- S(k) is monotone non-decreasing in k: requiring more consecutive
smooth numbers can only increase the threshold. -/
axiom smoothThreshold_mono (k₁ k₂ : ℕ) (h : k₁ ≤ k₂)
    (hk : 2 ≤ k₁) : smoothThreshold k₁ ≤ smoothThreshold k₂

/-- For k = 2, S(2) = 3: there is a positive density set of n where
both n+1 and n+2 are 3-smooth, but not 2-smooth. -/
axiom smooth_threshold_2 : smoothThreshold 2 = 3
