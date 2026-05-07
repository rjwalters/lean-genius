import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import Proofs.BezoutIdentityOQ01OQ01

/-
# Binary GCD Extended to Integers

## Open Question (bezout-identity-oq-01-oq-01-oq-02)

Can Stein's binary GCD algorithm be extended to handle integer inputs?

## What This Proves

The parent `BezoutIdentityOQ01OQ01` proves that `binaryGcd : ℕ → ℕ → ℕ` (Stein's
algorithm using subtraction and halving) equals `Nat.gcd`. This file extends to ℤ:

1. `intBinaryGcd` — defines the integer extension via `Int.natAbs`
2. `intBinaryGcd_eq_gcd` — equals Mathlib's `Int.gcd` (as integers)
3. `intBinaryGcd_nonneg` — non-negative
4. `intBinaryGcd_dvd_left/right` — divisibility in ℤ
5. `intBinaryGcd_comm` — symmetry
6. `intBinaryGcd_neg_left/right` — sign invariance
7. `intBinaryGcd_zero_left/right` — boundary cases
8. `bezout_via_intBinaryGcd` — Bézout identity: ∃ u v, u*a + v*b = intBinaryGcd a b
9. `dvd_intBinaryGcd` — any common divisor divides intBinaryGcd (via Bézout)

## Key Insight

`Int.gcd a b = Nat.gcd a.natAbs b.natAbs` (definitionally in Mathlib), so the
extension reduces immediately to the natural number algorithm. Sign does not affect GCD.
-/

namespace BezoutIdentityOQ01OQ01OQ02

open BezoutIdentityOQ01OQ01

-- ═══════════════════════════════════════════════════════════════
-- PART I: DEFINITION
-- ═══════════════════════════════════════════════════════════════

/-- The integer binary GCD: reduce to `natAbs` and apply Stein's algorithm.
Returns a non-negative integer equal to `(Int.gcd a b : ℤ)`. -/
def intBinaryGcd (a b : ℤ) : ℤ := ↑(binaryGcd a.natAbs b.natAbs)

-- ═══════════════════════════════════════════════════════════════
-- PART II: CORE PROPERTIES
-- ═══════════════════════════════════════════════════════════════

/-- `intBinaryGcd` equals Mathlib's `Int.gcd` (as an integer). -/
theorem intBinaryGcd_eq_gcd (a b : ℤ) :
    intBinaryGcd a b = (Int.gcd a b : ℤ) := by
  unfold intBinaryGcd; rw [binaryGcd_eq_gcd]; rfl

/-- `intBinaryGcd` is non-negative. -/
theorem intBinaryGcd_nonneg (a b : ℤ) : 0 ≤ intBinaryGcd a b := by
  simp only [intBinaryGcd]; positivity

/-- `intBinaryGcd a b` divides `a`. -/
theorem intBinaryGcd_dvd_left (a b : ℤ) : intBinaryGcd a b ∣ a :=
  intBinaryGcd_eq_gcd a b ▸ Int.gcd_dvd_left a b

/-- `intBinaryGcd a b` divides `b`. -/
theorem intBinaryGcd_dvd_right (a b : ℤ) : intBinaryGcd a b ∣ b :=
  intBinaryGcd_eq_gcd a b ▸ Int.gcd_dvd_right a b

/-- `intBinaryGcd` is symmetric. -/
theorem intBinaryGcd_comm (a b : ℤ) :
    intBinaryGcd a b = intBinaryGcd b a := by
  simp [intBinaryGcd, binaryGcd_comm]

-- ═══════════════════════════════════════════════════════════════
-- PART III: SIGN INVARIANCE
-- ═══════════════════════════════════════════════════════════════

/-- GCD is unaffected by negating the left argument. -/
theorem intBinaryGcd_neg_left (a b : ℤ) :
    intBinaryGcd (-a) b = intBinaryGcd a b := by
  simp [intBinaryGcd, Int.natAbs_neg]

/-- GCD is unaffected by negating the right argument. -/
theorem intBinaryGcd_neg_right (a b : ℤ) :
    intBinaryGcd a (-b) = intBinaryGcd a b := by
  simp [intBinaryGcd, Int.natAbs_neg]

/-- GCD depends only on absolute values. -/
theorem intBinaryGcd_natAbs (a b : ℤ) :
    intBinaryGcd a b = intBinaryGcd (a.natAbs : ℤ) (b.natAbs : ℤ) := by
  simp only [intBinaryGcd, Int.natAbs_natCast]

-- ═══════════════════════════════════════════════════════════════
-- PART IV: BOUNDARY CASES
-- ═══════════════════════════════════════════════════════════════

/-- `intBinaryGcd 0 b = |b|` (as an integer) -/
theorem intBinaryGcd_zero_left (b : ℤ) :
    intBinaryGcd 0 b = (b.natAbs : ℤ) := by
  unfold intBinaryGcd
  rw [Int.natAbs_zero, binaryGcd_eq_gcd, Nat.gcd_zero_left]

/-- `intBinaryGcd a 0 = |a|` (as an integer) -/
theorem intBinaryGcd_zero_right (a : ℤ) :
    intBinaryGcd a 0 = (a.natAbs : ℤ) := by
  unfold intBinaryGcd
  rw [Int.natAbs_zero, binaryGcd_eq_gcd, Nat.gcd_zero_right]

-- ═══════════════════════════════════════════════════════════════
-- PART V: BÉZOUT IDENTITY
-- ═══════════════════════════════════════════════════════════════

/-- **Integer Binary Bézout Identity**: For any `a b : ℤ`, there exist
`u v : ℤ` such that `u * a + v * b = intBinaryGcd a b`.

Proved via Mathlib's `Int.gcd_eq_gcd_ab` Bézout coefficients. -/
theorem bezout_via_intBinaryGcd (a b : ℤ) :
    ∃ u v : ℤ, u * a + v * b = intBinaryGcd a b := by
  refine ⟨Int.gcdA a b, Int.gcdB a b, ?_⟩
  have heq : intBinaryGcd a b = (Int.gcd a b : ℤ) := intBinaryGcd_eq_gcd a b
  have hbez : (Int.gcd a b : ℤ) = a * Int.gcdA a b + b * Int.gcdB a b :=
    Int.gcd_eq_gcd_ab a b
  rw [heq, hbez]
  ring

-- ═══════════════════════════════════════════════════════════════
-- PART VI: GCD PROPERTY
-- ═══════════════════════════════════════════════════════════════

/-- Any integer divisor of both `a` and `b` also divides `intBinaryGcd a b`.
Proved via the Bézout identity: d ∣ a ∧ d ∣ b → d ∣ u*a + v*b = intBinaryGcd a b. -/
theorem dvd_intBinaryGcd {d a b : ℤ} (ha : d ∣ a) (hb : d ∣ b) :
    d ∣ intBinaryGcd a b := by
  obtain ⟨u, v, h⟩ := bezout_via_intBinaryGcd a b
  rw [← h]
  exact dvd_add (dvd_mul_of_dvd_right ha u) (dvd_mul_of_dvd_right hb v)

-- ═══════════════════════════════════════════════════════════════
-- PART VII: COMPUTATIONAL EXAMPLES
-- ═══════════════════════════════════════════════════════════════

example : intBinaryGcd 12 8 = 4 := by native_decide
example : intBinaryGcd (-12) 8 = 4 := by native_decide
example : intBinaryGcd 12 (-8) = 4 := by native_decide
example : intBinaryGcd (-35) (-15) = 5 := by native_decide
example : intBinaryGcd 17 5 = 1 := by native_decide

end BezoutIdentityOQ01OQ01OQ02
