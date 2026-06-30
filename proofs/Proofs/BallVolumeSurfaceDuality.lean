/-
  OQ-02: Radial-Shell Decomposition — Volume as the Integral of Surface Area
  (circumference-via-differentiation-oq-02)

  The parent `CircumferenceViaDifferentiation` proves the *differential* half of
  the area–circumference duality, `d/dr(πr²) = 2πr`, and OQ-01 generalizes the
  derivative direction to every dimension, `d/dr(ω_n rⁿ) = n·ω_n·rⁿ⁻¹`. But the
  parent's own conclusion notes that the *integral* half —

      "A(r) = ∫₀ʳ C(t) dt — the disk read as a union of concentric circles"

  — is stated only informally and "does not separately formalize the integral."

  This file fills exactly that gap, in general dimension, via the Fundamental
  Theorem of Calculus:

      V_n(r) = ∫₀ʳ S_{n-1}(ρ) dρ            (radial-shell decomposition)
      V_n(b) − V_n(a) = ∫ₐᵇ S_{n-1}(ρ) dρ   (volume of an annular shell)

  where V_n and S_{n-1} are OQ-01's genuine n-ball volume and (n-1)-sphere
  surface functions (with ω_n = π^(n/2)/Γ(n/2+1)). The ball is literally the
  union of its concentric bounding spheres, and integrating their surface areas
  radially recovers the volume.

  Concrete consequences are double-checked by direct integration:
      ∫₀ʳ 2πρ dρ  = πr²        (n = 2, recovering the parent)
      ∫₀ʳ 4πρ² dρ = (4/3)πr³   (n = 3, the sphere)

  This is the antiderivative direction the parent and OQ-01 leave open; it is
  *not* a restatement of the derivative direction. Self-contained on top of
  OQ-01. Status: 0 sorries, 0 axioms (beyond Mathlib's).
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic
import Proofs.CircumferenceViaDifferentiationOQ01

open Real intervalIntegral
open CircumferenceViaDifferentiationOQ01

noncomputable section

namespace BallVolumeSurfaceDuality

/-
## Continuity of the surface function
-/

/-- The (n−1)-sphere surface function `S(ρ) = n·ω_n·ρⁿ⁻¹` is continuous: it is a
constant times a monomial. Needed for interval integrability in the FTC. -/
theorem nSphereSurfaceFn_continuous (n : ℕ) :
    Continuous (nSphereSurfaceFn n) := by
  unfold nSphereSurfaceFn
  fun_prop

/-
## The integral direction (Fundamental Theorem of Calculus)
-/

/-- The radial integral of the surface function over `[a, b]` telescopes to the
difference of volumes. Direct application of the FTC to OQ-01's core derivative
identity `dV/dr = S`. -/
theorem integral_surface_eq_sub (n : ℕ) (a b : ℝ) :
    ∫ ρ in a..b, nSphereSurfaceFn n ρ = nBallVolumeFn n b - nBallVolumeFn n a :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => nBallVolumeFn_hasDerivAt n x)
    ((nSphereSurfaceFn_continuous n).intervalIntegrable a b)

/-- **Annular-shell volume.** The volume of the shell `a ≤ |x| ≤ b` of the
n-ball equals the radial integral of the bounding-sphere surface area over
`[a, b]`. -/
theorem shell_volume_eq_integral (n : ℕ) (a b : ℝ) :
    nBallVolumeFn n b - nBallVolumeFn n a = ∫ ρ in a..b, nSphereSurfaceFn n ρ :=
  (integral_surface_eq_sub n a b).symm

/-- **Radial-shell decomposition** (the gap left open by the parent and OQ-01).
For `n ≥ 1`, the volume of the n-ball of radius `r` is the radial integral of the
surface area of its concentric bounding spheres:

  `V_n(r) = ∫₀ʳ S_{n-1}(ρ) dρ`.

The n-ball is the union of its concentric bounding spheres. -/
theorem nBallVolume_eq_integral (n : ℕ) (hn : 1 ≤ n) (r : ℝ) :
    nBallVolumeFn n r = ∫ ρ in (0 : ℝ)..r, nSphereSurfaceFn n ρ := by
  rw [integral_surface_eq_sub]
  have hz : nBallVolumeFn n 0 = 0 := by
    unfold nBallVolumeFn
    rw [zero_pow (by omega : n ≠ 0), mul_zero]
  rw [hz, sub_zero]

/-- **Volume–surface duality, both directions.** OQ-01 supplies the derivative
direction (`dV/dr = S`); this file supplies the integral direction
(`V = ∫₀ʳ S`). Together they are inverse statements of the same geometric fact. -/
theorem volume_surface_duality (n : ℕ) (hn : 1 ≤ n) (r : ℝ) :
    deriv (nBallVolumeFn n) r = nSphereSurfaceFn n r ∧
      nBallVolumeFn n r = ∫ ρ in (0 : ℝ)..r, nSphereSurfaceFn n ρ :=
  ⟨deriv_nBallVolume n r, nBallVolume_eq_integral n hn r⟩

/-
## Clean form of the integrand in low dimensions
-/

/-- The 1-sphere (circle) surface integrand is the circumference `2πρ`. -/
theorem nSphereSurfaceFn_two_eq (ρ : ℝ) : nSphereSurfaceFn 2 ρ = 2 * π * ρ := by
  unfold nSphereSurfaceFn
  rw [nSphereSurfaceConst_two, show (2 : ℕ) - 1 = 1 from rfl]
  ring

/-- The 2-sphere surface integrand is the spherical area `4πρ²`. -/
theorem nSphereSurfaceFn_three_eq (ρ : ℝ) : nSphereSurfaceFn 3 ρ = 4 * π * ρ ^ 2 := by
  unfold nSphereSurfaceFn
  rw [nSphereSurfaceConst_three, show (3 : ℕ) - 1 = 2 from rfl]

/-
## Concrete radial integrals, computed directly

These independently verify that integrating the surface area really reproduces
the classical volume formulas — a cross-check of the general theorem above.
-/

/-- `∫₀ʳ 2πρ dρ = πr²` — integrating the circumference recovers the disk area. -/
theorem circumference_integral_eq (r : ℝ) :
    (∫ ρ in (0 : ℝ)..r, 2 * π * ρ) = π * r ^ 2 := by
  rw [intervalIntegral.integral_const_mul, integral_id]
  ring

/-- `∫₀ʳ 4πρ² dρ = (4/3)πr³` — integrating the sphere surface recovers the
ball volume. -/
theorem sphere_surface_integral_eq (r : ℝ) :
    (∫ ρ in (0 : ℝ)..r, 4 * π * ρ ^ 2) = 4 * π / 3 * r ^ 3 := by
  rw [intervalIntegral.integral_const_mul, integral_pow]
  norm_num
  ring

/-- **n = 2 (parent recovery).** The disk area is the radial integral of the
circumference, with the integrand written explicitly: `πr² = ∫₀ʳ 2πρ dρ`. This
is precisely the integral form the parent states informally. -/
theorem disk_area_radial_shell (r : ℝ) :
    nBallVolumeFn 2 r = ∫ ρ in (0 : ℝ)..r, 2 * π * ρ := by
  rw [circumference_integral_eq]
  show unitBallVolume 2 * r ^ 2 = π * r ^ 2
  rw [unitBallVolume_two]

/-- **n = 3 (the sphere).** The ball volume is the radial integral of the
sphere's surface area, written explicitly: `(4/3)πr³ = ∫₀ʳ 4πρ² dρ`. -/
theorem ball_volume_radial_shell (r : ℝ) :
    nBallVolumeFn 3 r = ∫ ρ in (0 : ℝ)..r, 4 * π * ρ ^ 2 := by
  rw [sphere_surface_integral_eq]
  show unitBallVolume 3 * r ^ 3 = 4 * π / 3 * r ^ 3
  rw [unitBallVolume_three]

/-- Consistency of the two n = 2 presentations: the abstract surface integrand
`S_1` and the explicit circumference `2πρ` give the same integral. -/
theorem disk_area_presentations_agree (r : ℝ) :
    (∫ ρ in (0 : ℝ)..r, nSphereSurfaceFn 2 ρ) = ∫ ρ in (0 : ℝ)..r, 2 * π * ρ := by
  simp_rw [nSphereSurfaceFn_two_eq]

end BallVolumeSurfaceDuality

end -- noncomputable section
