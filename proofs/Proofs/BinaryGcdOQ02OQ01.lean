import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import Proofs.GCDAlgorithmOQ02

/-
# Binary GCD via Bit Operations (binary-gcd-oq-02-oq-01)

## Problem Statement
Can Stein's binary GCD algorithm be equivalently expressed using
hardware-level bit operations — `Nat.testBit 0` (LSB parity test)
and `Nat.shiftRight 1` (right shift = halve) — and still proved correct?

## Answer
Yes. The bit-operation formulation `binaryGcdBit` is provably equivalent to
both the arithmetic formulation `binaryGcd` and to `Nat.gcd`.

## Mathematical Significance
Modern bignum GCD implementations (GMP, OpenSSL, etc.) use:
- `n & 1` / `n.testBit 0` instead of `n % 2` to test parity (single AND)
- `n >> 1` / `n >>> 1` instead of `n / 2` for halving (single SHR)

This proof formally establishes that the bit-level algorithm spec
is equivalent to the mathematical definition of GCD.

## Key Lean 4 / Mathlib Lemmas Used
- `Nat.testBit_zero : testBit x 0 = decide (x % 2 = 1)`
- `Nat.mod_two_eq_zero_iff_testBit_zero : x % 2 = 0 ↔ x.testBit 0 = false`
- `Nat.shiftRight_succ : n >>> (k+1) = (n >>> k) / 2`
- `Nat.shiftRight_zero : n >>> 0 = n`

## Summary: 7 theorems, 0 sorries, 0 axioms
-/

namespace BinaryGcdBit

open BinaryGcd

/-! ## Part I: Bit Operation Bridge Lemmas -/

/-- Right shift by 1 equals integer halving: `n >>> 1 = n / 2`.
    Proof: `n >>> 1 = n >>> (0+1) = (n >>> 0) / 2 = n / 2`. -/
theorem shiftRight_one_eq_div_two (n : ℕ) : n >>> 1 = n / 2 := by
  have h := Nat.shiftRight_succ n 0
  simp [Nat.shiftRight_zero] at h
  exact h

/-- Even check via testBit: `n % 2 = 0 ↔ n.testBit 0 = false`.
    Wraps `Nat.mod_two_eq_zero_iff_testBit_zero` for local use. -/
theorem even_iff_testBit_zero_false (n : ℕ) : n % 2 = 0 ↔ n.testBit 0 = false :=
  Nat.mod_two_eq_zero_iff_testBit_zero

/-! ## Part II: The Bit-Level Binary GCD Algorithm -/

/-- **Binary GCD via Bit Operations** (`binaryGcdBit`):
    Computes GCD using `testBit 0` for parity and `>>> 1` for halving.
    Structurally identical to `BinaryGcd.binaryGcd` but uses bit ops.

    Each operation maps to a single machine instruction:
    - `n.testBit 0 = false` ↔ LSB is 0 ↔ n is even (one AND)
    - `n >>> 1` = right shift by 1 = halve (one SHR) -/
def binaryGcdBit : ℕ → ℕ → ℕ
  | 0, b => b
  | a, 0 => a
  | a + 1, b + 1 =>
    if ha : (a + 1).testBit 0 = false then
      if hb : (b + 1).testBit 0 = false then
        2 * binaryGcdBit ((a + 1) >>> 1) ((b + 1) >>> 1)
      else
        binaryGcdBit ((a + 1) >>> 1) (b + 1)
    else if hb : (b + 1).testBit 0 = false then
      binaryGcdBit (a + 1) ((b + 1) >>> 1)
    else if a + 1 > b + 1 then
      binaryGcdBit ((a + 1 - (b + 1)) >>> 1) (b + 1)
    else
      binaryGcdBit (a + 1) ((b + 1 - (a + 1)) >>> 1)
  termination_by a + b
  decreasing_by all_goals simp [shiftRight_one_eq_div_two]; omega

/-! ## Part III: Correctness -/

/-- Helper: from `n % 2 ≠ 0`, derive `n.testBit 0 ≠ false`. -/
private theorem testBit_ne_false_of_odd {n : ℕ} (h : ¬n % 2 = 0) :
    ¬n.testBit 0 = false :=
  fun htb => h ((even_iff_testBit_zero_false n).mpr htb)

/-- **Main Theorem**: The bit-operation GCD equals `Nat.gcd` on all inputs.

    Proof: Induction on the same recursive structure as `binaryGcd`, with
    bridge lemmas connecting testBit/shiftRight to the arithmetic ops.
    At each step, the bit-level and arithmetic computations agree because
    `testBit 0 = false ↔ even` and `>>> 1 = / 2`. -/
theorem binaryGcdBit_eq_gcd : ∀ a b : ℕ, binaryGcdBit a b = Nat.gcd a b := by
  intro a b
  induction a, b using binaryGcd.induct with
  | case1 b =>
    simp [binaryGcdBit, Nat.gcd_zero_left]
  | case2 a =>
    cases a with
    | zero => simp [binaryGcdBit]
    | succ a => simp [binaryGcdBit, Nat.gcd_zero_right]
  | case3 a b ha hb ih =>
    -- Both even: translate arithmetic conditions to bit conditions
    have ha' : (a + 1).testBit 0 = false := (even_iff_testBit_zero_false _).mp ha
    have hb' : (b + 1).testBit 0 = false := (even_iff_testBit_zero_false _).mp hb
    simp only [binaryGcdBit, dif_pos ha', dif_pos hb',
               shiftRight_one_eq_div_two, ih]
    -- 2 * Nat.gcd ((a+1)/2) ((b+1)/2) = Nat.gcd (a+1) (b+1)
    have ha2 : a + 1 = 2 * ((a + 1) / 2) := by omega
    have hb2 : b + 1 = 2 * ((b + 1) / 2) := by omega
    conv_rhs => rw [ha2, hb2]
    exact gcd_two_mul.symm
  | case4 a b ha hb ih =>
    -- a+1 even, b+1 odd
    have ha' : (a + 1).testBit 0 = false := (even_iff_testBit_zero_false _).mp ha
    have hb' : ¬(b + 1).testBit 0 = false := testBit_ne_false_of_odd hb
    simp only [binaryGcdBit, dif_pos ha', dif_neg hb',
               shiftRight_one_eq_div_two, ih]
    -- Nat.gcd ((a+1)/2) (b+1) = Nat.gcd (a+1) (b+1)
    have ha2 : a + 1 = 2 * ((a + 1) / 2) := by omega
    have hb1 : (b + 1) % 2 = 1 := by omega
    conv_rhs => rw [ha2]
    exact (gcd_mul_two_left hb1).symm
  | case5 a b ha hb ih =>
    -- a+1 odd, b+1 even
    have ha' : ¬(a + 1).testBit 0 = false := testBit_ne_false_of_odd ha
    have hb' : (b + 1).testBit 0 = false := (even_iff_testBit_zero_false _).mp hb
    simp only [binaryGcdBit, dif_neg ha', dif_pos hb',
               shiftRight_one_eq_div_two, ih]
    -- Nat.gcd (a+1) ((b+1)/2) = Nat.gcd (a+1) (b+1)
    have hb2 : b + 1 = 2 * ((b + 1) / 2) := by omega
    have ha1 : (a + 1) % 2 = 1 := by omega
    conv_rhs => rw [hb2]
    exact (gcd_mul_two_right ha1).symm
  | case6 a b ha hb hgt ih =>
    -- Both odd, a+1 > b+1
    have ha' : ¬(a + 1).testBit 0 = false := testBit_ne_false_of_odd ha
    have hb' : ¬(b + 1).testBit 0 = false := testBit_ne_false_of_odd hb
    simp only [binaryGcdBit, dif_neg ha', dif_neg hb', if_pos hgt,
               shiftRight_one_eq_div_two, ih]
    -- Nat.gcd ((a+1-(b+1))/2) (b+1) = Nat.gcd (a+1) (b+1)
    have ha1 : (a + 1) % 2 = 1 := by omega
    have hb1 : (b + 1) % 2 = 1 := by omega
    exact gcd_odd_sub_half ha1 hb1 hgt
  | case7 a b ha hb hle ih =>
    -- Both odd, a+1 ≤ b+1
    have ha' : ¬(a + 1).testBit 0 = false := testBit_ne_false_of_odd ha
    have hb' : ¬(b + 1).testBit 0 = false := testBit_ne_false_of_odd hb
    have hnotgt : ¬(a + 1 > b + 1) := by omega
    simp only [binaryGcdBit, dif_neg ha', dif_neg hb', if_neg hnotgt,
               shiftRight_one_eq_div_two, ih]
    -- Nat.gcd (a+1) ((b+1-(a+1))/2) = Nat.gcd (a+1) (b+1)
    have ha1 : (a + 1) % 2 = 1 := by omega
    have hb1 : (b + 1) % 2 = 1 := by omega
    exact gcd_odd_sub_half_right ha1 hb1 (by omega)

/-! ## Part IV: Properties (corollaries via correctness) -/

/-- Commutativity: bit-op GCD is symmetric. -/
theorem binaryGcdBit_comm (a b : ℕ) : binaryGcdBit a b = binaryGcdBit b a := by
  simp [binaryGcdBit_eq_gcd, Nat.gcd_comm]

/-- Identity elements. -/
theorem binaryGcdBit_zero_left (b : ℕ) : binaryGcdBit 0 b = b := by
  cases b <;> simp [binaryGcdBit]

theorem binaryGcdBit_zero_right (a : ℕ) : binaryGcdBit a 0 = a := by
  cases a <;> simp [binaryGcdBit]

/-- Concrete sanity checks via decidability. -/
example : binaryGcdBit 12 18 = 6 := by decide
example : binaryGcdBit 48 36 = 12 := by decide
example : binaryGcdBit 17 13 = 1 := by decide
example : binaryGcdBit 0 7 = 7 := by decide
example : binaryGcdBit 100 75 = 25 := by decide

end BinaryGcdBit
