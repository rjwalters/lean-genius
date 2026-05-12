/-
# Lehmer's GCD for Integers (binary-gcd-oq-02-oq-02)

## What This Proves
Extends the Lehmer GCD algorithm, originally defined on `ℕ` in
`Proofs/BinaryGcdOQ03OQ01.lean` (`LehmerGcdOQ01.lehmerGcd`), to integers `ℤ`.
The integer version is defined by reducing to absolute values and delegating
to the natural-number implementation, then proved equal to Mathlib's `Int.gcd`.

This is the Lehmer analogue of `BinaryGcdOQ02.binaryGcdInt` and closes the
"can the Lehmer algorithm be extended to ℤ?" question from `BinaryGcdOQ02`
(Erdős-style OQ-02 sub-tree).

## Why This Closes the Question
For integers the answer is "yes, mechanically": `Int.gcd` is already defined
on the absolute values (`Int.gcd a b = a.natAbs.gcd b.natAbs`), and the ℕ
Lehmer GCD is already proved correct (`LehmerGcdOQ01.lehmerGcd_correct`).
The integer extension therefore inherits correctness with no new content
beyond the `natAbs` reduction.

Unlike binary GCD on integers (purely formal correctness), Lehmer's GCD for
ℤ is the *production-relevant* extension: every multi-precision arithmetic
library that ships an integer-GCD routine (GMP, GnuMP, BigInt in JDK, etc.)
runs Lehmer on the absolute values, exactly as formalized here.

## What's NOT Covered
The "leading-digit quotient estimate" optimization (the actual content of
Lehmer's 1938 paper, which speeds up GCD on bignums by a constant factor) is
formalized separately in `BinaryGcdOQ03OQ02*` and is orthogonal to the ℤ
extension. The natAbs reduction proved here works regardless of whether the
underlying ℕ algorithm uses leading-digit estimation or naive Euclidean
descent.

## References
- Lehmer, D.H. (1938). "Euclid's Algorithm for Large Numbers." Amer. Math. Monthly.
- Knuth TAOCP §4.5.2 (Algorithm L, integer extension via |·|).
- Mathlib: `Int.gcd` (defined as `m.natAbs.gcd n.natAbs`).
- Companion: `Proofs/BinaryGcdOQ02.lean` (binary GCD, parallel pattern).
-/
import Mathlib.Data.Int.GCD
import Mathlib.Tactic
import Proofs.BinaryGcdOQ03OQ01

namespace BinaryGcdOQ02OQ02

open LehmerGcdOQ01

/-- **Lehmer's GCD on integers**: take absolute values, delegate to the
natural-number Lehmer GCD. The result lives in `ℕ` since `gcd ≥ 0` always. -/
def lehmerGcdInt (a b : ℤ) : ℕ := lehmerGcd a.natAbs b.natAbs

/-! ## Reduction to the natural-number version -/

/-- The integer Lehmer GCD reduces to the `ℕ` Lehmer GCD on absolute values. -/
@[simp] theorem lehmerGcdInt_natAbs (a b : ℤ) :
    lehmerGcdInt a b = lehmerGcd a.natAbs b.natAbs := rfl

/-- For non-negative integer arguments (cast from `ℕ`), `lehmerGcdInt`
agrees with the underlying natural Lehmer GCD. -/
theorem lehmerGcdInt_natCast (a b : ℕ) :
    lehmerGcdInt (a : ℤ) (b : ℤ) = lehmerGcd a b := by
  simp [lehmerGcdInt]

/-! ## Correctness against `Int.gcd` -/

/-- **Correctness**: `lehmerGcdInt` computes `Int.gcd`. -/
theorem lehmerGcdInt_eq_intGcd (a b : ℤ) :
    lehmerGcdInt a b = Int.gcd a b := by
  unfold lehmerGcdInt Int.gcd
  exact lehmerGcd_correct a.natAbs b.natAbs

/-! ## Sign invariance -/

/-- Negating the first argument leaves the Lehmer GCD unchanged. -/
@[simp] theorem lehmerGcdInt_neg_left (a b : ℤ) :
    lehmerGcdInt (-a) b = lehmerGcdInt a b := by
  simp [lehmerGcdInt]

/-- Negating the second argument leaves the Lehmer GCD unchanged. -/
@[simp] theorem lehmerGcdInt_neg_right (a b : ℤ) :
    lehmerGcdInt a (-b) = lehmerGcdInt a b := by
  simp [lehmerGcdInt]

/-- Negating both arguments leaves the Lehmer GCD unchanged. -/
theorem lehmerGcdInt_neg_neg (a b : ℤ) :
    lehmerGcdInt (-a) (-b) = lehmerGcdInt a b := by
  simp

/-! ## Edge cases -/

/-- `lehmerGcdInt 0 b = |b|`. -/
@[simp] theorem lehmerGcdInt_zero_left (b : ℤ) :
    lehmerGcdInt 0 b = b.natAbs := by
  simp [lehmerGcdInt, lehmerGcd_zero_left]

/-- `lehmerGcdInt a 0 = |a|`. -/
@[simp] theorem lehmerGcdInt_zero_right (a : ℤ) :
    lehmerGcdInt a 0 = a.natAbs := by
  simp [lehmerGcdInt, lehmerGcd_zero_right]

/-- Symmetry: `lehmerGcdInt a b = lehmerGcdInt b a`. -/
theorem lehmerGcdInt_comm (a b : ℤ) :
    lehmerGcdInt a b = lehmerGcdInt b a := by
  rw [lehmerGcdInt_eq_intGcd, lehmerGcdInt_eq_intGcd, Int.gcd_comm]

/-- Self-application: `lehmerGcdInt a a = |a|`. -/
@[simp] theorem lehmerGcdInt_self (a : ℤ) :
    lehmerGcdInt a a = a.natAbs := by
  rw [lehmerGcdInt_eq_intGcd, Int.gcd_self]

/-- The output is non-negative as a `ℕ` (trivially). -/
theorem lehmerGcdInt_nonneg (a b : ℤ) : 0 ≤ lehmerGcdInt a b := Nat.zero_le _

/-! ## Universal property

We prove the universal property of `lehmerGcdInt` by reducing to `natAbs`
and invoking `Nat.dvd_gcd` / `Nat.gcd_dvd_left` / `Nat.gcd_dvd_right`. This
keeps the proofs agnostic to whether Mathlib's `Int.gcd_dvd_*` lemmas
expose the divisor as `ℤ`- or `ℕ`-typed (the convention shifted in
recent Mathlib versions). -/

/-- `lehmerGcdInt` divides the first argument (in `ℤ`). -/
theorem lehmerGcdInt_dvd_left (a b : ℤ) :
    (lehmerGcdInt a b : ℤ) ∣ a := by
  -- Goal: ↑(lehmerGcd a.natAbs b.natAbs) ∣ a
  unfold lehmerGcdInt
  rw [lehmerGcd_correct]
  -- Goal: ↑(a.natAbs.gcd b.natAbs) ∣ a
  have h1 : a.natAbs.gcd b.natAbs ∣ a.natAbs := Nat.gcd_dvd_left _ _
  have h2 : (a.natAbs.gcd b.natAbs : ℤ) ∣ (a.natAbs : ℤ) :=
    Int.natCast_dvd_natCast.mpr h1
  -- `(↑a.natAbs : ℤ) ∣ a` via `Int.natAbs_dvd.mpr (dvd_refl a)`.
  exact h2.trans (Int.natAbs_dvd.mpr (dvd_refl a))

/-- `lehmerGcdInt` divides the second argument (in `ℤ`). -/
theorem lehmerGcdInt_dvd_right (a b : ℤ) :
    (lehmerGcdInt a b : ℤ) ∣ b := by
  unfold lehmerGcdInt
  rw [lehmerGcd_correct]
  have h1 : a.natAbs.gcd b.natAbs ∣ b.natAbs := Nat.gcd_dvd_right _ _
  have h2 : (a.natAbs.gcd b.natAbs : ℤ) ∣ (b.natAbs : ℤ) :=
    Int.natCast_dvd_natCast.mpr h1
  exact h2.trans (Int.natAbs_dvd.mpr (dvd_refl b))

/-- Universal property: any common divisor of `a` and `b` (in `ℤ`) divides
`lehmerGcdInt a b` (cast back into `ℤ`). -/
theorem dvd_lehmerGcdInt {a b c : ℤ} (ha : c ∣ a) (hb : c ∣ b) :
    c ∣ (lehmerGcdInt a b : ℤ) := by
  unfold lehmerGcdInt
  rw [lehmerGcd_correct]
  -- Goal: c ∣ ↑(a.natAbs.gcd b.natAbs)
  -- Step 1: c.natAbs divides each natAbs.
  have h1 : c.natAbs ∣ a.natAbs := Int.natAbs_dvd_natAbs.mpr ha
  have h2 : c.natAbs ∣ b.natAbs := Int.natAbs_dvd_natAbs.mpr hb
  -- Step 2: hence c.natAbs ∣ Nat.gcd a.natAbs b.natAbs.
  have h3 : c.natAbs ∣ a.natAbs.gcd b.natAbs := Nat.dvd_gcd h1 h2
  -- Step 3: lift to ℤ, and combine with c ∣ ↑c.natAbs.
  have h4 : (c.natAbs : ℤ) ∣ (a.natAbs.gcd b.natAbs : ℤ) :=
    Int.natCast_dvd_natCast.mpr h3
  exact (Int.dvd_natAbs.mpr (dvd_refl c)).trans h4

/-! ## Agreement with binary GCD on integers

Since both `BinaryGcdOQ02.binaryGcdInt` and `lehmerGcdInt` reduce to the
same `Int.gcd`, they compute the same value on every input. We can't import
`BinaryGcdOQ02` here without creating a dependency cycle (it imports
`GcdAlgorithmOQ02`, not `BinaryGcdOQ03OQ01`), so we state the agreement
abstractly via `Int.gcd`. -/

/-- Both Lehmer- and Mathlib-style integer GCDs agree. The corresponding
statement for `BinaryGcdOQ02.binaryGcdInt` follows by the same reasoning;
see `BinaryGcdOQ02.binaryGcdInt_eq_intGcd`. -/
theorem lehmerGcdInt_eq_natAbs_gcd (a b : ℤ) :
    lehmerGcdInt a b = a.natAbs.gcd b.natAbs := by
  rw [lehmerGcdInt_eq_intGcd]
  rfl

/-! ## Concrete sanity checks

Each example rewrites the Lehmer-flavoured integer GCD to `Int.gcd` (via the
correctness theorem) and then closes by `decide` — `Int.gcd` reduces to
`Nat.gcd` on `natAbs`, both of which are decidable on concrete numerals. -/

example : lehmerGcdInt 12 18 = 6 := by rw [lehmerGcdInt_eq_intGcd]; decide
example : lehmerGcdInt (-12) 18 = 6 := by rw [lehmerGcdInt_eq_intGcd]; decide
example : lehmerGcdInt 12 (-18) = 6 := by rw [lehmerGcdInt_eq_intGcd]; decide
example : lehmerGcdInt (-12) (-18) = 6 := by rw [lehmerGcdInt_eq_intGcd]; decide
example : lehmerGcdInt 0 7 = 7 := by rw [lehmerGcdInt_eq_intGcd]; decide
example : lehmerGcdInt 0 (-7) = 7 := by rw [lehmerGcdInt_eq_intGcd]; decide
example : lehmerGcdInt 17 17 = 17 := by rw [lehmerGcdInt_eq_intGcd]; decide
example : lehmerGcdInt (-17) 17 = 17 := by rw [lehmerGcdInt_eq_intGcd]; decide

/-! ## Summary

- **Integer extension**: complete and verified via `lehmerGcdInt_eq_intGcd`.
- **Bignum extension**: inherited "for free" from Lean's `Nat` (kernel uses
  GMP). The leading-digit quotient-estimate speedup (the substantive content
  of Lehmer's 1938 paper) is formalized separately in `BinaryGcdOQ03OQ02*`
  and is orthogonal to the ℤ extension proved here. -/

end BinaryGcdOQ02OQ02
