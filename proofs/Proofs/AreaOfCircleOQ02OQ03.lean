/-
  Surface Area of the Unit Sphere: S_n = n · V_n
  Open Question: area-of-circle-oq-02-oq-03
  Parent:        area-of-circle-oq-02  (N-Dimensional Ball Volume Formula)

  The parent `AreaOfCircleOQ02.lean` establishes the closed form for the volume of
  the unit n-ball,

      V_n = π^(n/2) / Γ(n/2 + 1).

  This file supplies the companion closed form for the (n-1)-dimensional measure of
  the unit sphere S^{n-1} (the boundary of the unit n-ball),

      S_n = 2 · π^(n/2) / Γ(n/2),

  and proves the classical scaling/divergence-theorem identity relating the two:

      S_n = n · V_n.                          (`surface_eq_n_mul_volume`)

  ## Why this is not a tautology

  An earlier gallery file (`AreaOfCircleOQ01OQ02OQ01.lean`) *defines* the surface
  area differentially, as `nSphereArea n r = n · ω_n · r^(n-1)`, the derivative of
  the volume; there `S = n·V` holds by definition.  Here, by contrast, the surface
  area is defined by its own independent Gamma closed form `2·π^(n/2)/Γ(n/2)`, the
  one-half-dimension-down analogue of the volume formula.  The identity `S_n = n·V_n`
  then carries genuine content: it is *exactly* the Gamma functional equation

      Γ(n/2 + 1) = (n/2) · Γ(n/2)

  in disguise.

  The edge case `n = 0` is handled by Mathlib's junk-value convention `Γ(0) = 0`:
  the surface formula gives `2/Γ(0) = 2/0 = 0`, which matches `0 · V_0 = 0`.

  Special values double-check the formula:
      S_1 = 2      (the two endpoints of [-1,1], a 0-dimensional measure)
      S_2 = 2π     (the circumference of the unit circle)
      S_3 = 4π     (the surface area of the unit sphere)

  Status: 0 sorries, 0 axioms (beyond Mathlib's foundations).

  References:
  - Mathlib: Real.Gamma_add_one, Real.Gamma_zero, Real.Gamma_one_half_eq, Real.Gamma_two
  - Classical: surface area of S^{n-1} = 2 π^(n/2) / Γ(n/2)
-/

import Mathlib

open MeasureTheory Real

namespace NSphereSurface

noncomputable section

/-- The unit n-ball volume `V_n = π^(n/2) / Γ(n/2 + 1)`.
    Matches `AreaOfCircleOQ02.unitBallVolume`; restated here to be self-contained. -/
def unitBallVolume (n : ℕ) : ℝ :=
  π ^ ((n : ℝ) / 2) / Gamma ((n : ℝ) / 2 + 1)

/-- The (n-1)-sphere surface measure `S_n = 2 · π^(n/2) / Γ(n/2)`, the
    one-half-dimension-down analogue of the volume formula. -/
def unitSphereSurface (n : ℕ) : ℝ :=
  2 * π ^ ((n : ℝ) / 2) / Gamma ((n : ℝ) / 2)

/-- `Γ(3/2) = √π / 2`, the value used for the odd-dimensional special cases. -/
private lemma gamma_three_div_two : Gamma (3 / 2 : ℝ) = √π / 2 := by
  have h := Real.Gamma_add_one (show (1 / 2 : ℝ) ≠ 0 from by norm_num)
  rw [show (1 : ℝ) / 2 + 1 = 3 / 2 from by ring] at h
  rw [h, Real.Gamma_one_half_eq]; ring

/-! ## Basic positivity -/

/-- The unit ball volume is positive. -/
theorem unitBallVolume_pos (n : ℕ) : 0 < unitBallVolume n := by
  unfold unitBallVolume
  exact div_pos (rpow_pos_of_pos pi_pos _) (Gamma_pos_of_pos (by positivity))

/-- For `n ≥ 1` the sphere surface is strictly positive. -/
theorem unitSphereSurface_pos {n : ℕ} (hn : 1 ≤ n) : 0 < unitSphereSurface n := by
  unfold unitSphereSurface
  have hgn : (0 : ℝ) < (n : ℝ) / 2 := by positivity
  refine div_pos ?_ (Gamma_pos_of_pos hgn)
  have : (0 : ℝ) < π ^ ((n : ℝ) / 2) := rpow_pos_of_pos pi_pos _
  linarith

/-! ## The main identity: `S_n = n · V_n` -/

/-- **Surface–volume scaling identity.**  The (n-1)-dimensional measure of the unit
    sphere equals `n` times the volume of the unit n-ball:

        2 · π^(n/2) / Γ(n/2)  =  n · ( π^(n/2) / Γ(n/2 + 1) ).

    This is the Gamma functional equation `Γ(n/2 + 1) = (n/2)·Γ(n/2)` made geometric.
    The `n = 0` case holds via Mathlib's convention `Γ(0) = 0` (both sides are `0`). -/
theorem surface_eq_n_mul_volume (n : ℕ) :
    unitSphereSurface n = (n : ℝ) * unitBallVolume n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp [unitSphereSurface, unitBallVolume, Real.Gamma_zero]
  · unfold unitSphereSurface unitBallVolume
    have hn2 : ((n : ℝ) / 2) ≠ 0 := by positivity
    have hgpos : (0 : ℝ) < Gamma ((n : ℝ) / 2) := Gamma_pos_of_pos (by positivity)
    rw [Real.Gamma_add_one hn2]
    field_simp

/-- The surface-to-volume ratio of the unit n-ball is exactly `n`. -/
theorem surface_div_volume (n : ℕ) :
    unitSphereSurface n / unitBallVolume n = (n : ℝ) := by
  rw [surface_eq_n_mul_volume, mul_div_assoc, div_self (ne_of_gt (unitBallVolume_pos n)),
      mul_one]

/-! ## Volume special values (mirroring the parent `AreaOfCircleOQ02`) -/

/-- `V_1 = 2` (length of `[-1, 1]`). -/
theorem unitBallVolume_one : unitBallVolume 1 = 2 := by
  unfold unitBallVolume
  simp only [Nat.cast_one]
  rw [show (1 : ℝ) / 2 + 1 = 3 / 2 from by ring, gamma_three_div_two,
      ← Real.sqrt_eq_rpow]
  have h : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  field_simp [h.ne']

/-- `V_2 = π` (area of the unit disk). -/
theorem unitBallVolume_two : unitBallVolume 2 = π := by
  unfold unitBallVolume
  rw [show ((2 : ℕ) : ℝ) / 2 + 1 = 2 from by norm_num,
      show ((2 : ℕ) : ℝ) / 2 = 1 from by norm_num, rpow_one, Real.Gamma_two, div_one]

/-- `V_3 = 4π/3` (volume of the unit ball). -/
theorem unitBallVolume_three : unitBallVolume 3 = 4 * π / 3 := by
  unfold unitBallVolume
  rw [show ((3 : ℕ) : ℝ) / 2 + 1 = 3 / 2 + 1 from by norm_num,
      Real.Gamma_add_one (show (3 / 2 : ℝ) ≠ 0 from by norm_num), gamma_three_div_two,
      show ((3 : ℕ) : ℝ) / 2 = 1 / 2 + 1 from by norm_num,
      Real.rpow_add Real.pi_pos, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have h : (0 : ℝ) < √π := Real.sqrt_pos.mpr Real.pi_pos
  have hsq : √π * √π = π := Real.mul_self_sqrt (le_of_lt Real.pi_pos)
  field_simp
  nlinarith [hsq, h]

/-! ## Surface special values (via the main identity) -/

/-- `S_1 = 2`: the boundary of `[-1, 1]` is two points, total `0`-measure `2`. -/
theorem unitSphereSurface_one : unitSphereSurface 1 = 2 := by
  rw [surface_eq_n_mul_volume, unitBallVolume_one]; norm_num

/-- `S_2 = 2π`: the circumference of the unit circle. -/
theorem unitSphereSurface_two : unitSphereSurface 2 = 2 * π := by
  rw [surface_eq_n_mul_volume, unitBallVolume_two]; push_cast; ring

/-- `S_3 = 4π`: the surface area of the unit sphere. -/
theorem unitSphereSurface_three : unitSphereSurface 3 = 4 * π := by
  rw [surface_eq_n_mul_volume, unitBallVolume_three]; push_cast; ring

/-- A direct check that the surface *closed form* (not the identity) gives the
    circumference at `n = 2`: `2 · π^1 / Γ(1) = 2π`. -/
theorem unitSphereSurface_two_direct : unitSphereSurface 2 = 2 * π := by
  unfold unitSphereSurface
  rw [show ((2 : ℕ) : ℝ) / 2 = 1 from by norm_num, rpow_one, Real.Gamma_one, div_one]

end

end NSphereSurface
