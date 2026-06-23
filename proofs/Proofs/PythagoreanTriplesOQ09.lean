/-
Integer Inradius of a Pythagorean Right Triangle

Source: Open question from pythagorean-triples gallery proof
Status: VERIFIED (0 axioms, 0 sorries)

A right triangle whose legs `x, y` and hypotenuse `z` form a Pythagorean triple
(`x² + y² = z²`) has an inradius

        r = (x + y − z) / 2

that is a *non-negative integer*. This is a small but genuinely geometric
integrality phenomenon: the radius of the inscribed circle of an integer right
triangle is itself an integer. Three ingredients:

  * **Parity** — `2 ∣ (x + y − z)` for ANY Pythagorean triple. Reducing
    `x² + y² = z²` modulo 2 and using `a² = a` in `ZMod 2` gives `x + y ≡ z`,
    so `x + y − z` is even. (No coprimality or mod-4 case split is needed; this
    is cleaner than the mod-4 obstruction used for the single-leg parity in
    `PythagoreanTriplesOQ07`.)

  * **Positivity** — `z ≤ x + y` for non-negative legs, since
    `(x + y)² = z² + 2xy ≥ z²`. Hence `r = (x + y − z)/2 ≥ 0`.

  * **Area identity** — `(x + y − z)(x + y + z) = 2xy`, obtained by expanding
    `(x + y)² − z² = 2xy`. Writing `x + y − z = 2r` and `x + y + z = 2s` (the
    semiperimeter is `s`), this becomes `2·r·s = xy`, i.e. `r·s = xy/2 = Area`.
    This is the classical `Area = r·s` for a right triangle.

Distinct from `PythagoreanTriplesOQ07` (single-leg parity dichotomy under
coprimality): here we extract a geometric integrality invariant valid for every
triple, plus the inradius–semiperimeter–area relation.
-/

import Mathlib

namespace PythagoreanTriplesInradius

open PythagoreanTriple

variable {x y z : ℤ}

/-! ## Part I: Parity — `2 ∣ (x + y − z)`

Reduce `x² + y² = z²` modulo 2. In `ZMod 2` every element satisfies `a² = a`,
so the equation collapses to `x + y = z`, i.e. `x + y − z ≡ 0 (mod 2)`. -/

/-- For ANY Pythagorean triple, `x + y − z` is even. No coprimality needed. -/
theorem dvd_two_add_sub (h : PythagoreanTriple x y z) : (2 : ℤ) ∣ (x + y - z) := by
  have he : x * x + y * y = z * z := h
  have key : ∀ a : ZMod 2, a * a = a := by decide
  -- push the triple equation into `ZMod 2`
  have hcast : (x : ZMod 2) * x + (y : ZMod 2) * y = (z : ZMod 2) * z := by
    have := congrArg (fun t : ℤ => (t : ZMod 2)) he
    push_cast at this
    exact this
  rw [key, key, key] at hcast
  -- now `x + y = z` in `ZMod 2`, so `x + y − z = 0`
  have hzero : ((x + y - z : ℤ) : ZMod 2) = 0 := by
    push_cast
    rw [hcast]; ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp hzero

/-- Corollary: `x + y + z` is also even (it differs from `x + y − z` by `2z`). -/
theorem dvd_two_add_add (h : PythagoreanTriple x y z) : (2 : ℤ) ∣ (x + y + z) := by
  obtain ⟨r, hr⟩ := dvd_two_add_sub h
  exact ⟨r + z, by linarith [hr]⟩

/-! ## Part II: The area identity

`(x + y − z)(x + y + z) = (x + y)² − z² = 2xy`, using `x² + y² = z²`. -/

/-- **Area identity.** `(x + y − z)(x + y + z) = 2xy` for any Pythagorean triple. -/
theorem inradius_identity (h : PythagoreanTriple x y z) :
    (x + y - z) * (x + y + z) = 2 * (x * y) := by
  have he : x * x + y * y = z * z := h
  linear_combination he

/-! ## Part III: Positivity — `z ≤ x + y`

For non-negative legs, `(x + y)² = z² + 2xy ≥ z²`, hence `z ≤ x + y`, so the
inradius `(x + y − z)/2` is non-negative. -/

/-- For a triple with non-negative entries, the hypotenuse is at most the sum of
the legs (the triangle inequality, here forced by `x² + y² = z²`). -/
theorem hyp_le_add (h : PythagoreanTriple x y z)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) : z ≤ x + y := by
  have he : x * x + y * y = z * z := h
  nlinarith [mul_nonneg hx hy, mul_nonneg (add_nonneg hx hy) hz,
    mul_nonneg hx hz, mul_nonneg hy hz, sq_nonneg (x + y - z)]

/-! ## Part IV: The inradius is a non-negative integer

Packaging the facts: there is a *non-negative integer* `r` (the inradius) with
`x + y − z = 2r`, and it satisfies the area relation `r·(x + y + z) = x·y`,
i.e. `r·s = Area` where `s = (x + y + z)/2` is the semiperimeter and the area is
`x·y/2`. -/

/-- The area relation: if `x + y − z = 2r` then `r·(x + y + z) = x·y`.
Since the perimeter is `x + y + z = 2s` and the area is `x·y/2`, this is exactly
`r·s = Area`. -/
theorem inradius_area (h : PythagoreanTriple x y z) {r : ℤ}
    (hr : x + y - z = 2 * r) : r * (x + y + z) = x * y := by
  have hid := inradius_identity h
  rw [hr] at hid
  -- hid : (2 * r) * (x + y + z) = 2 * (x * y)
  have h2 : 2 * (r * (x + y + z)) = 2 * (x * y) := by linear_combination hid
  exact mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h2

/-- **Inradius integrality + area relation.** For an integer right triangle with
non-negative sides there is a *non-negative integer* `r` (the inradius) with
`x + y − z = 2r` and `r·(x + y + z) = x·y` (the classical `Area = r·s`). -/
theorem inradius (h : PythagoreanTriple x y z)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    ∃ r : ℤ, 0 ≤ r ∧ x + y - z = 2 * r ∧ r * (x + y + z) = x * y := by
  obtain ⟨r, hr⟩ := dvd_two_add_sub h
  have hle := hyp_le_add h hx hy hz
  exact ⟨r, by omega, hr, inradius_area h hr⟩

/-! ## Part V: The inradius of a primitive triple

For a primitively-classified triple with the standard parametrisation
`x = m² − n²`, `y = 2mn`, `z = m² + n²`, the inradius is `r = n(m − n)`. -/

/-- For the standard parametrisation of a primitive triple
`x = m² − n²`, `y = 2mn`, `z = m² + n²`, the inradius equals `n(m − n)`:
explicitly `x + y − z = 2·n·(m − n)`. -/
theorem inradius_param (m n : ℤ) :
    (m ^ 2 - n ^ 2) + 2 * m * n - (m ^ 2 + n ^ 2) = 2 * (n * (m - n)) := by
  ring

end PythagoreanTriplesInradius
