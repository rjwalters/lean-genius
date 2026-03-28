/-
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
import Mathlib.Data.Nat.Choose.Basic

open Finset

/-- Decidability of natural number divisibility (needed for native_decide). -/
instance Nat.decidableDvd' (m n : ℕ) : Decidable (m ∣ n) :=
  decidable_of_iff (n % m = 0) Nat.dvd_iff_mod_eq_zero.symm

/- ## Core Definitions -/

/-- Product of k consecutive integers starting at n:
  n · (n+1) · ··· · (n+k−1) -/
def consecutiveProd (n k : ℕ) : ℕ :=
  ∏ i ∈ Finset.range k, (n + i)

/-- The divisibility condition: the "lower block" n·(n+1)···(n+k−1)
divides the "upper block" (n+k)·(n+k+1)···(n+2k−1). -/
abbrev divides_upper_block (n k : ℕ) : Prop :=
  consecutiveProd n k ∣ consecutiveProd (n + k) k

/-- The minimal k ≥ 1 satisfying the divisibility for a given n.
    Returns 0 if no such k exists (conjectured to never happen). -/
noncomputable def minimalK (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ divides_upper_block n k}

/- ## Main Conjecture -/

/-- **Erdős Problem #389 (OPEN).**
For every n ≥ 1, there exists k ≥ 1 such that
  n(n+1)···(n+k−1) ∣ (n+k)(n+k+1)···(n+2k−1).
Stated as a definition since this is an open problem. -/
def ErdosProblem389 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ divides_upper_block n k

/- ## Small Cases -/

/-- n = 1, k = 1: trivially 1 ∣ 2. -/
theorem erdos_389_n1 : divides_upper_block 1 1 := by
  simp [divides_upper_block, consecutiveProd]

/-- n = 2, k = 5: 2·3·4·5·6 = 720 divides 7·8·9·10·11 = 55440. -/
theorem erdos_389_n2 : divides_upper_block 2 5 := by native_decide

/-- n = 3, k = 4: 3·4·5·6 = 360 divides 7·8·9·10 = 5040. -/
theorem erdos_389_n3 : divides_upper_block 3 4 := by native_decide

/- ## Mehta's Computation -/

/-- **Bhavik Mehta's computation.**
The minimal k for n = 4 is 207. This is the smallest k such that
  4·5···210 ∣ 211·212···417.
  PROVED by native_decide (bignum arithmetic). -/
theorem mehta_n4_minimal :
  1 ≤ (207 : ℕ) ∧ divides_upper_block 4 207 := ⟨by omega, by native_decide⟩

/-- No smaller k works for n = 4.
    PROVED by reducing to a finite check over Finset.Ico 1 207
    and using native_decide for bignum divisibility checks. -/
theorem mehta_n4_minimality :
    ∀ k : ℕ, 1 ≤ k → k < 207 → ¬ divides_upper_block 4 k := by
  suffices ∀ k ∈ Finset.Ico 1 207, ¬ divides_upper_block 4 k from
    fun k hk1 hk207 => this k (Finset.mem_Ico.mpr ⟨hk1, hk207⟩)
  native_decide

/- ## Ratio Interpretation -/

/- **The upper block relates to binomial coefficients.**
    consecutiveProd n k = n · (n+1) · ··· · (n+k-1) = k! · C(n+k-1, k).
    This connects the divisibility problem to binomial coefficient arithmetic.

    Note: The previous `ratio_identity` axiom was vacuously true (used
    `∨ ¬ divides_upper_block n k` as an escape clause). Replaced with the
    cleaner binomial identity. -/

/-- Helper: consecutiveProd recurrence. -/
private lemma consecutiveProd_succ (n k : ℕ) :
    consecutiveProd n (k + 1) = consecutiveProd n k * (n + k) := by
  simp [consecutiveProd, Finset.prod_range_succ]

/-- The product of consecutive integers relates to binomial coefficients:
  consecutiveProd n k = k! · C(n+k−1, k). -/
theorem consecutiveProd_binomial (n k : ℕ) (hn : 0 < n) :
    consecutiveProd n k = k.factorial * (n + k - 1).choose k := by
  induction k with
  | zero => simp [consecutiveProd]
  | succ k ih =>
    rw [consecutiveProd_succ, ih]
    rw [show n + (k + 1) - 1 = n + k from by omega, Nat.factorial_succ]
    have h := Nat.add_one_mul_choose_eq (n + k - 1) k
    rw [show n + k - 1 + 1 = n + k from by omega] at h
    nlinarith
