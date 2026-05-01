/-
# Binary GCD for Integers (OQ-02)

## What This Proves
Extends the Binary GCD algorithm (Stein 1967), originally defined on `ℕ` in
`Proofs/GcdAlgorithmOQ02.lean`, to integers `ℤ`. The integer version is
defined by reducing to absolute values and delegating to the natural-number
implementation, then proved equal to Mathlib's `Int.gcd`.

This resolves the integer half of Erdős-style open question OQ-02 ("can the
binary GCD be extended to integers / bignums?"). The bignum half is deferred
as a separate (project-scale) sub-problem; see knowledge.md.

## Why This Closes the Question
For integers the answer is "yes, mechanically": gcd is defined on the
absolute values, and binary GCD on `ℕ` is already proved correct
(`BinaryGcd.binaryGcd_eq_gcd`). The integer extension therefore inherits
correctness with no new content beyond the `natAbs` reduction.

## References
- Stein (1967), Knuth TAOCP §4.5.2
- Mathlib: `Int.gcd` (defined as `m.natAbs.gcd n.natAbs`)
-/
import Mathlib.Data.Int.GCD
import Mathlib.Tactic
import Proofs.GcdAlgorithmOQ02

namespace BinaryGcdOQ02

open BinaryGcd

/-- **Binary GCD on integers**: take absolute values, delegate to the
natural-number binary GCD. The result lives in `ℕ` since `gcd ≥ 0` always. -/
def binaryGcdInt (a b : ℤ) : ℕ := binaryGcd a.natAbs b.natAbs

/-! ## Reduction to the natural-number version -/

/-- The integer binary GCD reduces to the `ℕ` binary GCD on absolute values. -/
@[simp] theorem binaryGcdInt_natAbs (a b : ℤ) :
    binaryGcdInt a b = binaryGcd a.natAbs b.natAbs := rfl

/-- For non-negative integer arguments (cast from `ℕ`), `binaryGcdInt`
agrees with the underlying natural binary GCD. -/
theorem binaryGcdInt_natCast (a b : ℕ) :
    binaryGcdInt (a : ℤ) (b : ℤ) = binaryGcd a b := by
  simp [binaryGcdInt]

/-! ## Correctness against `Int.gcd` -/

/-- **Correctness**: `binaryGcdInt` computes `Int.gcd`. -/
theorem binaryGcdInt_eq_intGcd (a b : ℤ) :
    binaryGcdInt a b = Int.gcd a b := by
  unfold binaryGcdInt Int.gcd
  exact binaryGcd_eq_gcd a.natAbs b.natAbs

/-! ## Sign invariance -/

/-- Negating the first argument leaves the binary GCD unchanged. -/
@[simp] theorem binaryGcdInt_neg_left (a b : ℤ) :
    binaryGcdInt (-a) b = binaryGcdInt a b := by
  simp [binaryGcdInt]

/-- Negating the second argument leaves the binary GCD unchanged. -/
@[simp] theorem binaryGcdInt_neg_right (a b : ℤ) :
    binaryGcdInt a (-b) = binaryGcdInt a b := by
  simp [binaryGcdInt]

/-- Negating both arguments leaves the binary GCD unchanged. -/
theorem binaryGcdInt_neg_neg (a b : ℤ) :
    binaryGcdInt (-a) (-b) = binaryGcdInt a b := by
  simp

/-! ## Edge cases -/

/-- `binaryGcdInt 0 b = |b|`. -/
@[simp] theorem binaryGcdInt_zero_left (b : ℤ) :
    binaryGcdInt 0 b = b.natAbs := by
  simp [binaryGcdInt, binaryGcd_zero_left]

/-- `binaryGcdInt a 0 = |a|`. -/
@[simp] theorem binaryGcdInt_zero_right (a : ℤ) :
    binaryGcdInt a 0 = a.natAbs := by
  simp [binaryGcdInt, binaryGcd_zero_right]

/-- Symmetry: `binaryGcdInt a b = binaryGcdInt b a`. -/
theorem binaryGcdInt_comm (a b : ℤ) :
    binaryGcdInt a b = binaryGcdInt b a := by
  rw [binaryGcdInt_eq_intGcd, binaryGcdInt_eq_intGcd, Int.gcd_comm]

/-- Self-application: `binaryGcdInt a a = |a|`. -/
@[simp] theorem binaryGcdInt_self (a : ℤ) :
    binaryGcdInt a a = a.natAbs := by
  rw [binaryGcdInt_eq_intGcd, Int.gcd_self]

/-- The output is non-negative as a `ℕ` (trivially). -/
theorem binaryGcdInt_nonneg (a b : ℤ) : 0 ≤ binaryGcdInt a b := Nat.zero_le _

/-- `binaryGcdInt` divides both arguments (in `ℤ`). -/
theorem binaryGcdInt_dvd_left (a b : ℤ) :
    (binaryGcdInt a b : ℤ) ∣ a := by
  rw [binaryGcdInt_eq_intGcd]
  exact Int.gcd_dvd_left

theorem binaryGcdInt_dvd_right (a b : ℤ) :
    (binaryGcdInt a b : ℤ) ∣ b := by
  rw [binaryGcdInt_eq_intGcd]
  exact Int.gcd_dvd_right

/-- Universal property: any common divisor divides `binaryGcdInt`. -/
theorem dvd_binaryGcdInt {a b c : ℤ} (ha : c ∣ a) (hb : c ∣ b) :
    c ∣ (binaryGcdInt a b : ℤ) := by
  rw [binaryGcdInt_eq_intGcd]
  exact Int.dvd_gcd ha hb

/-! ## Concrete sanity checks -/

example : binaryGcdInt 12 18 = 6 := by decide
example : binaryGcdInt (-12) 18 = 6 := by decide
example : binaryGcdInt 12 (-18) = 6 := by decide
example : binaryGcdInt (-12) (-18) = 6 := by decide
example : binaryGcdInt 0 7 = 7 := by decide
example : binaryGcdInt 0 (-7) = 7 := by decide
example : binaryGcdInt 17 17 = 17 := by decide
example : binaryGcdInt (-17) 17 = 17 := by decide

/-! ## Summary

- Integer extension: **complete and verified** via `binaryGcdInt_eq_intGcd`.
- Bignum extension: **deferred**. Lean's `Nat` is already unbounded (kernel
  uses GMP), so the algorithm runs on bignums "for free". A formal
  bit-sequence equivalence proof would be project-scale (~200+ lines) and
  is out of scope for this entry. -/

end BinaryGcdOQ02
