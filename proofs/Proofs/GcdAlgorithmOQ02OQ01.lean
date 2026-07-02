import Mathlib

/-
# Step Count of Binary GCD (Stein's Algorithm)

## What This Proves

The parent entry (`Proofs.GcdAlgorithmOQ02`) defines Stein's binary GCD as a
well-founded recursion `binaryGcd` and proves it computes `Nat.gcd`.  Its guard
structure (the three parity/comparison cases below) is reproduced verbatim here
as `binaryGcdSteps`.  The parent leaves open the *complexity* question:

> Can the step count of binary GCD be formally bounded?  The algorithm should
> take at most `2·log₂(max a b)` recursive steps.

This entry answers it.  We define `binaryGcdSteps`, the number of recursive
calls performed by the *same* case analysis that drives `binaryGcd`, and prove
the sharp logarithmic bound:

* `binaryGcdSteps_le_size_add` — the master bound
    `binaryGcdSteps a b ≤ Nat.size a + Nat.size b`,
  proved by a single induction on the recursion: **every** recursive branch
  strictly decreases the total bit length `size a + size b`.
* `binaryGcdSteps_le_two_mul_size_max` — the classical form
    `binaryGcdSteps a b ≤ 2 · Nat.size (max a b)`.

Since `Nat.size n = ⌊log₂ n⌋ + 1` for `n ≥ 1`, this is exactly the textbook
`O(log(max a b))` step count (Knuth, TAOCP 4.5.2; Brent 1976).  We also record
`binaryGcdSteps_pow_two_self`, showing the bound has the right order: on the
diagonal `(2^k, 2^k)` the algorithm uses exactly `k + 1` steps.

## Mathematical Content

The whole argument rests on one bit-length fact, `size_div_two_succ_le`:
halving a positive number drops its `Nat.size` by exactly one, i.e.
`(n / 2).size + 1 ≤ n.size`.  Each of the five recursive branches of the
algorithm either halves an operand (drops `size` by 1) or, in the odd–odd
branch, replaces the larger operand `A` by `(A - B)/2 ≤ A/2`, whose size is
again strictly smaller than `size A`.  Hence `size a + size b` is a decreasing
potential that starts below `size a + size b` and reaches `0` in at most that
many steps.
-/

namespace BinaryGcd

open Nat

/-! ## Part I: The step-count function

`binaryGcdSteps a b` counts the recursive calls of `binaryGcd a b`.  It is the
literal step-annotated copy of `binaryGcd`: identical guards, identical
recursive arguments, with each recursive case contributing `1`. -/

/-- Number of recursive calls made by `binaryGcd a b` (its recursion depth
along the actual reduction path). -/
def binaryGcdSteps : ℕ → ℕ → ℕ
  | 0, _ => 0
  | _ + 1, 0 => 0
  | a + 1, b + 1 =>
    if ha : (a + 1) % 2 = 0 then
      if hb : (b + 1) % 2 = 0 then
        1 + binaryGcdSteps ((a + 1) / 2) ((b + 1) / 2)
      else
        1 + binaryGcdSteps ((a + 1) / 2) (b + 1)
    else if hb : (b + 1) % 2 = 0 then
      1 + binaryGcdSteps (a + 1) ((b + 1) / 2)
    else if a + 1 > b + 1 then
      1 + binaryGcdSteps ((a + 1 - (b + 1)) / 2) (b + 1)
    else
      1 + binaryGcdSteps (a + 1) ((b + 1 - (a + 1)) / 2)
  termination_by a b => a + b
  decreasing_by all_goals omega

@[simp] theorem binaryGcdSteps_zero_left (b : ℕ) : binaryGcdSteps 0 b = 0 := by
  simp [binaryGcdSteps]

@[simp] theorem binaryGcdSteps_zero_right (a : ℕ) : binaryGcdSteps a 0 = 0 := by
  cases a <;> simp [binaryGcdSteps]

/-! ## Part II: The key bit-length lemma

Halving a positive natural number decreases `Nat.size` by exactly one. -/

/-- For `n ≥ 1`, `Nat.size (n / 2) + 1 ≤ Nat.size n`.  (Equivalently
`size (n/2) = size n - 1`; the inequality form is all we need.) -/
theorem size_div_two_succ_le {n : ℕ} (hn : 1 ≤ n) : (n / 2).size + 1 ≤ n.size := by
  rw [Nat.add_one_le_iff, Nat.lt_size]
  -- Goal: `2 ^ (n / 2).size ≤ n`.
  rcases Nat.eq_zero_or_pos (n / 2).size with hs | hs
  · rw [hs]; simpa using hn
  · -- `2 ^ (size (n/2) - 1) ≤ n/2`, then double.
    have h1 : 2 ^ ((n / 2).size - 1) ≤ n / 2 :=
      Nat.lt_size.mp (by omega)
    have hpow : (2 : ℕ) ^ (n / 2).size = 2 * 2 ^ ((n / 2).size - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega

/-- If `m < n` then `Nat.size (m / 2) + 1 ≤ Nat.size n`.  This absorbs the
odd–odd branch, where the new operand `(A - B)/2` can even be `0`. -/
theorem size_half_lt {m n : ℕ} (h : m < n) : (m / 2).size + 1 ≤ n.size := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simpa [Nat.size_zero] using Nat.size_pos.mpr (by omega : 0 < n)
  · calc (m / 2).size + 1 ≤ m.size := size_div_two_succ_le hm
      _ ≤ n.size := Nat.size_le_size (le_of_lt h)

/-! ## Part III: The logarithmic step bound

Master bound: the recursion depth never exceeds the total bit length. -/

/-- **Master step bound.**  `binaryGcd a b` performs at most `size a + size b`
recursive calls.  Proof: every recursive branch drops the potential
`size a + size b` by at least one. -/
theorem binaryGcdSteps_le_size_add (a b : ℕ) :
    binaryGcdSteps a b ≤ a.size + b.size := by
  induction a, b using binaryGcdSteps.induct with
  | case1 b => simp
  | case2 a => simp
  | case3 a b ha hb ih =>
    simp only [binaryGcdSteps, Nat.succ_eq_add_one, ha, hb, ↓reduceDIte]
    have h1 := size_div_two_succ_le (show 1 ≤ a + 1 by omega)
    have h2 := size_div_two_succ_le (show 1 ≤ b + 1 by omega)
    omega
  | case4 a b ha hb ih =>
    simp only [binaryGcdSteps, Nat.succ_eq_add_one, ha, hb, ↓reduceDIte]
    have h1 := size_div_two_succ_le (show 1 ≤ a + 1 by omega)
    omega
  | case5 a b ha hb ih =>
    simp only [binaryGcdSteps, Nat.succ_eq_add_one, ha, hb, ↓reduceDIte]
    have h2 := size_div_two_succ_le (show 1 ≤ b + 1 by omega)
    omega
  | case6 a b ha hb hgt ih =>
    simp only [binaryGcdSteps, Nat.succ_eq_add_one, ha, hb, hgt, ↓reduceDIte, ↓reduceIte]
    have h1 := size_half_lt (show a + 1 - (b + 1) < a + 1 by omega)
    omega
  | case7 a b ha hb hle ih =>
    simp only [binaryGcdSteps, Nat.succ_eq_add_one, ha, hb, ↓reduceDIte, ↓reduceIte, show ¬(a + 1 > b + 1) from by omega]
    have h1 := size_half_lt (show b + 1 - (a + 1) < b + 1 by omega)
    omega

/-- **Classical form.**  `binaryGcd a b` uses at most `2 · size (max a b)`
recursive steps.  Because `size n = ⌊log₂ n⌋ + 1` for `n ≥ 1`, this is the
textbook `O(log (max a b))` bound. -/
theorem binaryGcdSteps_le_two_mul_size_max (a b : ℕ) :
    binaryGcdSteps a b ≤ 2 * (max a b).size := by
  have h := binaryGcdSteps_le_size_add a b
  have ha : a.size ≤ (max a b).size := Nat.size_le_size (le_max_left a b)
  have hb : b.size ≤ (max a b).size := Nat.size_le_size (le_max_right a b)
  omega

/-! ## Part IV: Order tightness on the diagonal

The bound is of the right logarithmic order: on `(2^k, 2^k)` the algorithm
takes exactly `k + 1` steps, versus the upper bound `2·size (2^k) = 2(k+1)`. -/

/-- The recursion equation on doubled, positive inputs (both even). -/
theorem binaryGcdSteps_two_mul_two_mul (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    binaryGcdSteps (2 * a) (2 * b) = 1 + binaryGcdSteps a b := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha.ne'
  obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  rw [show 2 * (a + 1) = (2 * a + 1) + 1 by ring,
      show 2 * (b + 1) = (2 * b + 1) + 1 by ring]
  conv_lhs => rw [binaryGcdSteps]
  simp only [show (2 * a + 1 + 1) % 2 = 0 by omega,
             show (2 * b + 1 + 1) % 2 = 0 by omega, ↓reduceDIte]
  rw [show (2 * a + 1 + 1) / 2 = a + 1 by omega,
      show (2 * b + 1 + 1) / 2 = b + 1 by omega]

/-- `binaryGcdSteps 1 1 = 1` (the base of the diagonal family). -/
theorem binaryGcdSteps_one_one : binaryGcdSteps 1 1 = 1 := by
  conv_lhs => rw [show (1 : ℕ) = 0 + 1 from rfl, binaryGcdSteps]
  norm_num

/-- **Tightness.**  On the diagonal `(2^k, 2^k)` the step count is exactly
`k + 1`, matching the `Θ(log)` order of the upper bound. -/
theorem binaryGcdSteps_pow_two_self (k : ℕ) :
    binaryGcdSteps (2 ^ k) (2 ^ k) = k + 1 := by
  induction k with
  | zero => simpa using binaryGcdSteps_one_one
  | succ k ih =>
    rw [pow_succ, mul_comm (2 ^ k) 2,
        binaryGcdSteps_two_mul_two_mul _ _ (by positivity) (by positivity), ih]
    omega

end BinaryGcd
