import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-
# Weitzenböck's Inequality

## What This Proves
For any triangle with side lengths `a, b, c` and area `T`,
  `a² + b² + c² ≥ 4·√3·T`,
with equality **iff** the triangle is equilateral (`a = b = c`).

## Approach
The proof is entirely algebraic. We take Heron's identity in its squared form
  `16·T² = 2a²b² + 2b²c² + 2c²a² − a⁴ − b⁴ − c⁴`
as the definition of the (squared) area, square the target to
  `(a² + b² + c²)² ≥ 48·T²`,
and discharge the resulting polynomial inequality, which is the sum-of-squares
identity
  `(a²+b²+c²)² − 48T² = 2·((a²−b²)² + (b²−c²)² + (c²−a²)²) ≥ 0`.
The √3 is handled by `Real.sqrt_sq` once both sides are known nonnegative; the
equality case follows because the SOS vanishes exactly when `a² = b² = c²`.

This is not a named Mathlib result.
-/

namespace WeitzenbockInequalityOQ01

/-- Heron's area identity, squared and scaled by 16:
`16·T² = 2a²b² + 2b²c² + 2c²a² − a⁴ − b⁴ − c⁴`. We take this as the algebraic
definition of the squared area of a triangle with sides `a, b, c`. -/
def heronArea16Sq (a b c : ℝ) : ℝ :=
  2 * a ^ 2 * b ^ 2 + 2 * b ^ 2 * c ^ 2 + 2 * c ^ 2 * a ^ 2
    - a ^ 4 - b ^ 4 - c ^ 4

/-- The arithmetic core: `x² + y² + z² ≥ xy + yz + zx` for all reals. -/
theorem sos_core (x y z : ℝ) : x * y + y * z + z * x ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x)]

/-- For nonnegative reals, equality of squares implies equality. -/
theorem eq_of_sq_eq_sq {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u ^ 2 = v ^ 2) :
    u = v := by
  have h1 : Real.sqrt (u ^ 2) = Real.sqrt (v ^ 2) := by rw [h]
  rwa [Real.sqrt_sq hu, Real.sqrt_sq hv] at h1

/-- Squared form of Weitzenböck's inequality: `(a²+b²+c²)² ≥ 48·T²`. -/
theorem weitzenbock_sq (a b c T : ℝ) (hT : 16 * T ^ 2 = heronArea16Sq a b c) :
    48 * T ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
  have h48 : 48 * T ^ 2 = 3 * (16 * T ^ 2) := by ring
  rw [h48, hT]
  unfold heronArea16Sq
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
    sq_nonneg (c ^ 2 - a ^ 2)]

/-- **Weitzenböck's inequality.** For a triangle with side lengths `a, b, c` and
area `T` (given by Heron's formula), `a² + b² + c² ≥ 4·√3·T`. -/
theorem weitzenbock (a b c T : ℝ) (hTnn : 0 ≤ T)
    (hT : 16 * T ^ 2 = heronArea16Sq a b c) :
    4 * Real.sqrt 3 * T ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hlhs : 0 ≤ 4 * Real.sqrt 3 * T := by positivity
  have hrhs : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by positivity
  have hsqlhs : (4 * Real.sqrt 3 * T) ^ 2 = 48 * T ^ 2 := by
    have h : (4 * Real.sqrt 3 * T) ^ 2 = 16 * Real.sqrt 3 ^ 2 * T ^ 2 := by ring
    rw [h, hs]; ring
  have hcore : (4 * Real.sqrt 3 * T) ^ 2 ≤ (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
    rw [hsqlhs]; exact weitzenbock_sq a b c T hT
  calc 4 * Real.sqrt 3 * T
      = Real.sqrt ((4 * Real.sqrt 3 * T) ^ 2) := (Real.sqrt_sq hlhs).symm
    _ ≤ Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2) ^ 2) := Real.sqrt_le_sqrt hcore
    _ = a ^ 2 + b ^ 2 + c ^ 2 := Real.sqrt_sq hrhs

/-- **Equality case.** For a triangle with positive sides, Weitzenböck's
inequality is an equality iff the triangle is equilateral. -/
theorem weitzenbock_eq_iff (a b c T : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hTnn : 0 ≤ T) (hT : 16 * T ^ 2 = heronArea16Sq a b c) :
    4 * Real.sqrt 3 * T = a ^ 2 + b ^ 2 + c ^ 2 ↔ a = b ∧ b = c := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hlhs : 0 ≤ 4 * Real.sqrt 3 * T := by positivity
  have hrhs : 0 ≤ a ^ 2 + b ^ 2 + c ^ 2 := by positivity
  have hsqlhs : (4 * Real.sqrt 3 * T) ^ 2 = 48 * T ^ 2 := by
    have h : (4 * Real.sqrt 3 * T) ^ 2 = 16 * Real.sqrt 3 ^ 2 * T ^ 2 := by ring
    rw [h, hs]; ring
  -- Reduce the √3 equality to the polynomial equality `48T² = (a²+b²+c²)²`.
  have hsqiff : 4 * Real.sqrt 3 * T = a ^ 2 + b ^ 2 + c ^ 2
      ↔ 48 * T ^ 2 = (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 := by
    constructor
    · intro h; rw [← hsqlhs, h]
    · intro h; exact eq_of_sq_eq_sq hlhs hrhs (by rw [hsqlhs, h])
  rw [hsqiff, show (48 : ℝ) * T ^ 2 = 3 * (16 * T ^ 2) by ring, hT]
  unfold heronArea16Sq
  constructor
  · intro h
    have hle1 : (a ^ 2 - b ^ 2) ^ 2 ≤ 0 := by
      nlinarith [h, sq_nonneg (b ^ 2 - c ^ 2), sq_nonneg (c ^ 2 - a ^ 2)]
    have hle2 : (b ^ 2 - c ^ 2) ^ 2 ≤ 0 := by
      nlinarith [h, sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (c ^ 2 - a ^ 2)]
    have e1 : (a ^ 2 - b ^ 2) ^ 2 = 0 := le_antisymm hle1 (sq_nonneg _)
    have e2 : (b ^ 2 - c ^ 2) ^ 2 = 0 := le_antisymm hle2 (sq_nonneg _)
    have hab2 : a ^ 2 = b ^ 2 :=
      sub_eq_zero.mp (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp e1)
    have hbc2 : b ^ 2 = c ^ 2 :=
      sub_eq_zero.mp (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0) |>.mp e2)
    exact ⟨eq_of_sq_eq_sq ha.le hb.le hab2, eq_of_sq_eq_sq hb.le hc.le hbc2⟩
  · rintro ⟨hab, hbc⟩
    rw [hab, hbc]; ring

end WeitzenbockInequalityOQ01
