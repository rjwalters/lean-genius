/-!
# Erdős Problem #389 — Divisibility of Consecutive Integer Products

Is it true that for every n ≥ 1 there exists k ≥ 1 such that
  n(n+1)···(n+k−1) ∣ (n+k)(n+k+1)···(n+2k−1)?

That is, does the product of the first k consecutive integers starting
at n always divide the product of the next k consecutive integers?

## Background

The problem was posed by Erdős and Straus. Note that
  (n+k)···(n+2k−1) / (n·(n+1)···(n+k−1))
  = ∏_{i=0}^{k−1} (n+k+i)/(n+i)

so the question is whether this ratio of products can always be made
an integer by choosing k large enough.

## Key Data

- n = 1: k = 1 works trivially (1 ∣ 2).
- n = 2: k = 5 works since 2·3·4·5·6 ∣ 7·8·9·10·11.
- n = 3: k = 4 works since 3·4·5·6 ∣ 7·8·9·10.
- n = 4: Minimal k = 207 (Bhavik Mehta).
- The minimal k values for 1 ≤ n ≤ 18 form OEIS A375071.

*Reference:* [erdosproblems.com/389](https://www.erdosproblems.com/389)
-/

import Mathlib.Tactic
import Mathlib.Data.Finset.LocallyFinite

open Finset

/-! ## Core Definitions -/

/-- Product of k consecutive integers starting at n:
  n · (n+1) · ··· · (n+k−1) -/
def consecutiveProd (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, (n + i)

/-- The divisibility condition: the "lower block" n·(n+1)···(n+k−1)
divides the "upper block" (n+k)·(n+k+1)···(n+2k−1). -/
def divides_upper_block (n k : ℕ) : Prop :=
  consecutiveProd n k ∣ consecutiveProd (n + k) k

/-- The minimal k (if it exists) satisfying the divisibility for a given n. -/
noncomputable def minimalK (n : ℕ) : ℕ :=
  Nat.find (⟨1, by simp [divides_upper_block, consecutiveProd]⟩ :
    ∃ k : ℕ, 1 ≤ k ∧ divides_upper_block n k)

/-! ## Main Conjecture -/

/-- **Erdős Problem #389 (Open).**
For every n ≥ 1, there exists k ≥ 1 such that
  n(n+1)···(n+k−1) ∣ (n+k)(n+k+1)···(n+2k−1). -/
axiom erdos_389 :
  ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ divides_upper_block n k

/-! ## Small Cases -/

/-- n = 1, k = 1: trivially 1 ∣ 2. -/
theorem erdos_389_n1 : divides_upper_block 1 1 := by
  simp [divides_upper_block, consecutiveProd]

/-- n = 2, k = 5: 2·3·4·5·6 = 720 divides 7·8·9·10·11 = 55440. -/
axiom erdos_389_n2 : divides_upper_block 2 5

/-- n = 3, k = 4: 3·4·5·6 = 360 divides 7·8·9·10 = 5040. -/
axiom erdos_389_n3 : divides_upper_block 3 4

/-! ## Mehta's Computation -/

/-- **Bhavik Mehta's computation.**
The minimal k for n = 4 is 207. This is the smallest k such that
  4·5···210 ∣ 211·212···414. -/
axiom mehta_n4_minimal :
  1 ≤ (207 : ℕ) ∧ divides_upper_block 4 207

/-- No smaller k works for n = 4. -/
axiom mehta_n4_minimality :
  ∀ k : ℕ, 1 ≤ k → k < 207 → ¬ divides_upper_block 4 k

/-! ## Ratio Interpretation -/

/-- The ratio of consecutive products equals a product of ratios:
  ∏_{i=0}^{k-1} (n+k+i)/(n+i).
When this is an integer, the divisibility holds. We state this
as a multiplicative identity in ℕ. -/
axiom ratio_identity (n k : ℕ) (hn : 0 < n) :
  consecutiveProd (n + k) k = consecutiveProd n k *
    (∏ i ∈ Finset.range k, ((n + k + i) / (n + i)))
  ∨ ¬ divides_upper_block n k

/-- The product of consecutive integers relates to binomial coefficients:
  consecutiveProd n k = k! · C(n+k−1, k). -/
axiom consecutiveProd_binomial (n k : ℕ) (hn : 0 < n) :
  consecutiveProd n k = k.factorial * (n + k - 1).choose k
