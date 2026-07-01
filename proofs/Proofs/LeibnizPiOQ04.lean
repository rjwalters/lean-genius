import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic

/-!
# Euler's Two-Term Machin-Like Identity: π/4 = arctan(1/2) + arctan(1/3)

## What This Proves
Euler's classical decomposition of the quarter-turn angle into two arctangents of
unit fractions:

  π/4 = arctan(1/2) + arctan(1/3)

This is the simplest nontrivial *Machin-like* identity: it writes the angle whose
tangent is `1` (namely `arctan 1 = π/4`, the endpoint of the Leibniz/Gregory series
`π/4 = 1 - 1/3 + 1/5 - ⋯`) as a sum of two arctangents of *smaller* arguments, whose
own arctangent series converge geometrically faster.

## The General Characterization
Rather than verify the single numerical identity, we prove the underlying
**characterization theorem**. For positive reals `x, y`,

  arctan x + arctan y = π/4   ⟺   x + y + x·y = 1   ⟺   (1 + x)(1 + y) = 2.

Euler's identity is then the instance `x = 1/2, y = 1/3`, checked by the arithmetic
`1/2 + 1/3 + 1/6 = 1` (equivalently `(3/2)(4/3) = 2`).

The characterization exposes the whole one-parameter *family* of two-term π/4
identities: any `x ∈ (0, 1)` pairs with the unique `y = (1 - x)/(1 + x) > 0`.
Euler's `(1/2, 1/3)` is the value `x = 1/2`.

## Approach
- `Real.arctan_add : x*y < 1 → arctan x + arctan y = arctan ((x+y)/(1-x*y))` is the
  tangent addition formula transported through `arctan`.
- The forward direction needs `x < 1` and `y < 1` (hence `x*y < 1`), obtained from
  strict monotonicity of `arctan`: if `arctan x + arctan y = π/4` with `y > 0` then
  `arctan x < π/4 = arctan 1`.
- `Real.arctan_eq_pi_div_four : arctan x = π/4 ↔ x = 1` closes both directions.

## Status
- [x] Complete proof, 0 sorries, 0 axioms (foundational axioms only).
- [x] Parent: `leibniz-pi` (π/4 = arctan 1). This OQ splits that angle.

## Parent
Open question `leibniz-pi-oq-04` off the verified 0-axiom `leibniz-pi` entry.
-/

namespace LeibnizPiOQ04

open Real

/-- **Two-term π/4 characterization.** For positive reals `x` and `y`,
`arctan x + arctan y = π/4` holds exactly when `x + y + x·y = 1`. -/
theorem arctan_add_eq_pi_div_four_iff {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    arctan x + arctan y = π / 4 ↔ x + y + x * y = 1 := by
  constructor
  · -- Forward: from the angle sum, deduce x < 1, y < 1, then invert arctan_add.
    intro h
    -- `arctan y > 0` since `y > 0`, so `arctan x < π/4 = arctan 1`, giving `x < 1`.
    have hay : 0 < arctan y := arctan_pos.mpr hy
    have hax : 0 < arctan x := arctan_pos.mpr hx
    have hx1 : x < 1 := by
      have : arctan x < arctan 1 := by
        rw [arctan_one]; linarith
      exact (arctan_lt_arctan_iff).mp this
    have hy1 : y < 1 := by
      have : arctan y < arctan 1 := by
        rw [arctan_one]; linarith
      exact (arctan_lt_arctan_iff).mp this
    have hxy : x * y < 1 := by nlinarith
    -- Rewrite the sum through `arctan_add`, then peel off `arctan`.
    rw [arctan_add hxy] at h
    have hden : (1 - x * y) ≠ 0 := by nlinarith
    have hone := (arctan_eq_pi_div_four).mp h        -- (x + y)/(1 - x*y) = 1
    field_simp [hden] at hone
    nlinarith [hone]
  · -- Backward: `x + y + x*y = 1` forces the argument of `arctan_add` to be `1`.
    intro h
    have hxy : x * y < 1 := by nlinarith
    rw [arctan_add hxy]
    have hden : (1 - x * y) ≠ 0 := by nlinarith
    have harg : (x + y) / (1 - x * y) = 1 := by
      field_simp [hden]
      linarith
    rw [harg, arctan_one]

/-- **Product form of the characterization.** For positive reals,
`arctan x + arctan y = π/4` holds exactly when `(1 + x)(1 + y) = 2`. -/
theorem arctan_add_eq_pi_div_four_iff_prod {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    arctan x + arctan y = π / 4 ↔ (1 + x) * (1 + y) = 2 := by
  rw [arctan_add_eq_pi_div_four_iff hx hy]
  constructor <;> intro h <;> nlinarith [h]

/-- **Euler's identity.** `π/4 = arctan(1/2) + arctan(1/3)`, the simplest
two-term Machin-like decomposition of the quarter angle. -/
theorem euler_arctan_half_add_third :
    arctan (1 / 2) + arctan (1 / 3) = π / 4 := by
  rw [arctan_add_eq_pi_div_four_iff (by norm_num) (by norm_num)]
  norm_num

/-- Restatement splitting `arctan 1 = π/4` (the Leibniz endpoint) into two faster
arctangent series. -/
theorem arctan_one_eq_half_add_third :
    arctan 1 = arctan (1 / 2) + arctan (1 / 3) := by
  rw [arctan_one, euler_arctan_half_add_third]

/-- The pairing partner is explicit: any `x ∈ (0,1)` matches the unique
`y = (1 - x)/(1 + x) > 0`, exhibiting the whole family of two-term π/4 identities.
Euler's identity is the case `x = 1/2`, where `y = 1/3`. -/
theorem arctan_add_partner_eq_pi_div_four {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    arctan x + arctan ((1 - x) / (1 + x)) = π / 4 := by
  have hy : 0 < (1 - x) / (1 + x) := by
    apply div_pos <;> linarith
  have h1x : (1 + x) ≠ 0 := ne_of_gt (by linarith)
  rw [arctan_add_eq_pi_div_four_iff hx0 hy]
  field_simp [h1x]
  ring

end LeibnizPiOQ04
