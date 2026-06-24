/-
  # The discriminant of a quadratic via Vieta's formulas
  # (vietas-formulas-oq-04)

  ## The Open Question

  Vieta's formulas relate the coefficients of a polynomial to its roots. For a
  quadratic `a·x² + b·x + c` with roots `r, s` (and `a ≠ 0`), the relations are

      r + s = -b/a,      r·s = c/a,        equivalently   b = -a(r + s),  c = a·r·s.

  The parent entry `vietas-formulas` packages these relations. This file answers the
  open question: **express the discriminant `Δ = b² − 4ac` directly in terms of the
  roots and prove that a quadratic has a repeated root exactly when `Δ = 0`.**

  The key identity is purely algebraic:

      b² − 4ac = a²·(r − s)².

  From it everything follows: `Δ = 0 ⇔ r = s` over any field, `Δ ≥ 0` always over an
  ordered field (it is a square), and `Δ > 0 ⇔ r ≠ s` (distinct real roots).

  We also close the loop with `vieta_from_roots`, which *derives* the Vieta relations
  `b = -a(r+s)`, `c = a·r·s` from the mere fact that `r ≠ s` are both roots — so the
  discriminant identity holds for any quadratic with two distinct roots in the field.

  ## Axiom count: 0
-/

import Mathlib

namespace VietaDiscriminant

/-- **The discriminant identity (over any commutative ring).**
    Substituting the Vieta relations `b = -a(r+s)`, `c = a·r·s` into `b² − 4ac`
    collapses, by a single ring computation, to `a²·(r − s)²`. -/
theorem discriminant_eq {R : Type*} [CommRing R] (a b c r s : R)
    (hb : b = -a * (r + s)) (hc : c = a * (r * s)) :
    b ^ 2 - 4 * a * c = a ^ 2 * (r - s) ^ 2 := by
  subst hb hc; ring

/-- **Vieta relations from two distinct roots (over a field).**
    If `r ≠ s` are both roots of `a·x² + b·x + c`, then necessarily
    `b = -a(r + s)` and `c = a·r·s`. Subtracting the two root equations gives
    `(r − s)·(a(r+s) + b) = 0`; cancelling the nonzero factor `r − s` yields the
    formula for `b`, and back-substitution yields the formula for `c`. -/
theorem vieta_from_roots {F : Type*} [Field F] {a b c r s : F}
    (hr : a * r ^ 2 + b * r + c = 0) (hs : a * s ^ 2 + b * s + c = 0)
    (hrs : r ≠ s) :
    b = -a * (r + s) ∧ c = a * (r * s) := by
  -- Difference of the two root equations factors through `r − s`.
  have key : (r - s) * (a * (r + s) + b) = 0 := by linear_combination hr - hs
  have hrs' : r - s ≠ 0 := sub_ne_zero.mpr hrs
  have hbz : a * (r + s) + b = 0 := (mul_eq_zero.mp key).resolve_left hrs'
  have hb : b = -a * (r + s) := by linear_combination hbz
  refine ⟨hb, ?_⟩
  -- Back-substitute `b` into the first root equation to solve for `c`.
  rw [hb] at hr
  linear_combination hr

/-- **Discriminant from two distinct roots.** Combining the two results above:
    for any quadratic with distinct roots `r ≠ s` in a field, `b² − 4ac = a²(r−s)²`. -/
theorem discriminant_eq_of_roots {F : Type*} [Field F] {a b c r s : F}
    (hr : a * r ^ 2 + b * r + c = 0) (hs : a * s ^ 2 + b * s + c = 0)
    (hrs : r ≠ s) :
    b ^ 2 - 4 * a * c = a ^ 2 * (r - s) ^ 2 := by
  obtain ⟨hb, hc⟩ := vieta_from_roots hr hs hrs
  exact discriminant_eq a b c r s hb hc

/-- **Repeated root criterion (over a field).** With `a ≠ 0`, the discriminant
    vanishes exactly when the two roots coincide: `b² − 4ac = 0 ⇔ r = s`. -/
theorem discriminant_zero_iff {F : Type*} [Field F] {a b c r s : F}
    (ha : a ≠ 0) (hb : b = -a * (r + s)) (hc : c = a * (r * s)) :
    b ^ 2 - 4 * a * c = 0 ↔ r = s := by
  rw [discriminant_eq a b c r s hb hc]
  constructor
  · intro h
    have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
    have hsq : (r - s) ^ 2 = 0 := (mul_eq_zero.mp h).resolve_left ha2
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · intro h; subst h; ring

/-- **Nonnegativity over an ordered field.** Since the discriminant equals the
    square `a²(r−s)²`, it is always `≥ 0` when the roots lie in the field. -/
theorem discriminant_nonneg {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {a b c r s : F}
    (hb : b = -a * (r + s)) (hc : c = a * (r * s)) :
    0 ≤ b ^ 2 - 4 * a * c := by
  rw [discriminant_eq a b c r s hb hc]
  positivity

/-- **Strict positivity ⇔ distinct roots (over an ordered field).**
    With `a ≠ 0`, the discriminant is strictly positive exactly when the roots
    are distinct — the familiar "two distinct real roots ⇔ Δ > 0" dichotomy. -/
theorem discriminant_pos_iff_distinct {F : Type*} [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] {a b c r s : F}
    (ha : a ≠ 0) (hb : b = -a * (r + s)) (hc : c = a * (r * s)) :
    0 < b ^ 2 - 4 * a * c ↔ r ≠ s := by
  rw [discriminant_eq a b c r s hb hc]
  constructor
  · intro h hrs
    subst hrs; simp at h
  · intro hrs
    have hrs' : r - s ≠ 0 := sub_ne_zero.mpr hrs
    have h1 : 0 < a ^ 2 := by positivity
    have h2 : 0 < (r - s) ^ 2 := by positivity
    exact mul_pos h1 h2

/-!
## Concrete examples
-/

section Examples

/-- `x² − 5x + 6` has roots `2, 3`: here `a = 1, b = −5, c = 6` and
    `Δ = 25 − 24 = 1 = 1²·(3 − 2)²`. -/
example : ((-5 : ℚ)) ^ 2 - 4 * 1 * 6 = (1 : ℚ) ^ 2 * (3 - 2) ^ 2 := by norm_num

/-- A perfect square `x² − 4x + 4 = (x − 2)²` has the repeated root `2` and `Δ = 0`. -/
example : ((-4 : ℚ)) ^ 2 - 4 * 1 * 4 = 0 := by norm_num

/-- `x² + 1` (roots `±i`, not real) has `Δ = −4 < 0` over `ℚ`. -/
example : ((0 : ℚ)) ^ 2 - 4 * 1 * 1 < 0 := by norm_num

end Examples

end VietaDiscriminant

/-
  ## Summary

  | Result | Statement |
  |--------|-----------|
  | `discriminant_eq`              | `b² − 4ac = a²(r − s)²` from the Vieta relations (any `CommRing`) |
  | `vieta_from_roots`             | `r ≠ s` roots ⟹ `b = -a(r+s)`, `c = a·r·s` (field) |
  | `discriminant_eq_of_roots`     | `b² − 4ac = a²(r − s)²` from distinct roots (field) |
  | `discriminant_zero_iff`        | `a ≠ 0 ⟹ (Δ = 0 ⇔ r = s)` (repeated root) |
  | `discriminant_nonneg`          | `0 ≤ Δ` over a `LinearOrderedField` |
  | `discriminant_pos_iff_distinct`| `a ≠ 0 ⟹ (0 < Δ ⇔ r ≠ s)` (distinct real roots) |

  Everything reduces to the single ring identity `b² − 4ac = a²(r − s)²`.

  **Sorries**: 0
  **Axioms**: 0
-/
