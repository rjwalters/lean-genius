import Proofs.CevasTheoremNonEuclidean
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Ceva non-Euclidean OQ-01: the unified curvature-κ framework via sin_κ

The parent entry (`cevas-theorem-non-euclidean`) proves Ceva's theorem in Euclidean,
spherical, and hyperbolic geometry, unified through an arbitrary "distance function" `ρ`
in `ceva_unified_principle`. It lists as an open question:

> *Can the unified Ceva framework be extended to arbitrary curvature κ using the functions
> `sin_κ` (the Jacobi/curvature sine for curvature κ)?*

This file answers it. We define the **curvature sine**

`sin_κ(x) = sin(√κ · x)/√κ` (κ > 0),  `x` (κ = 0),  `sinh(√(−κ) · x)/√(−κ)` (κ < 0),

show it specializes to `sin` (κ = 1), `sinh` (κ = −1), and the identity (κ = 0), and prove
the **single curvature-parametrised Ceva theorem** `kappa_ceva` by instantiating the
parent's `ceva_unified_principle` at `ρ = sin_κ`. The classical spherical, hyperbolic, and
Euclidean Ceva theorems all fall out as the cases κ = 1, −1, 0.

## Main results

* `sinKappa` : the curvature sine `sin_κ`.
* `sinKappa_one` / `sinKappa_neg_one` / `sinKappa_zero` : specializations to `sin`, `sinh`, id.
* `sinKappa_pos` : positivity of `sin_κ(x)` for `0 < x` (with the spherical range condition).
* `kappa_ceva` : the unified curvature-κ Ceva theorem.
* `kappa_ceva_spherical` / `kappa_ceva_hyperbolic` / `kappa_ceva_euclidean` : the three
  classical cases recovered.
-/

namespace CevasNonEuclideanOQ01

open Real

/-- **The curvature sine `sin_κ`.** Interpolates the three constant-curvature geometries:
    `sin_κ(x) = sin(√κ·x)/√κ` for `κ > 0` (spherical), `x` for `κ = 0` (Euclidean), and
    `sinh(√(−κ)·x)/√(−κ)` for `κ < 0` (hyperbolic). -/
noncomputable def sinKappa (κ x : ℝ) : ℝ :=
  if 0 < κ then Real.sin (Real.sqrt κ * x) / Real.sqrt κ
  else if κ < 0 then Real.sinh (Real.sqrt (-κ) * x) / Real.sqrt (-κ)
  else x

/-- At curvature `κ = 1` the curvature sine is the ordinary sine (spherical/unit case). -/
theorem sinKappa_one (x : ℝ) : sinKappa 1 x = Real.sin x := by
  unfold sinKappa
  rw [if_pos (by norm_num : (0 : ℝ) < 1), Real.sqrt_one]
  simp

/-- At curvature `κ = −1` the curvature sine is the hyperbolic sine (hyperbolic case). -/
theorem sinKappa_neg_one (x : ℝ) : sinKappa (-1) x = Real.sinh x := by
  unfold sinKappa
  rw [if_neg (by norm_num : ¬(0 : ℝ) < -1), if_pos (by norm_num : (-1 : ℝ) < 0)]
  norm_num

/-- At curvature `κ = 0` the curvature sine is the identity (Euclidean case). -/
theorem sinKappa_zero (x : ℝ) : sinKappa 0 x = x := by
  unfold sinKappa
  rw [if_neg (lt_irrefl 0), if_neg (lt_irrefl 0)]

/-- **Positivity of `sin_κ`.** For a positive argument `x`, `sin_κ(x) > 0`. In the
    spherical case `κ > 0` one needs `√κ·x < π` (the segment is shorter than half the
    great circle); the hyperbolic and Euclidean cases are unconditional. -/
theorem sinKappa_pos (κ x : ℝ) (hx : 0 < x)
    (hsph : 0 < κ → Real.sqrt κ * x < Real.pi) : 0 < sinKappa κ x := by
  unfold sinKappa
  split_ifs with h1 h2
  · have hsqrt : 0 < Real.sqrt κ := Real.sqrt_pos.mpr h1
    exact div_pos (Real.sin_pos_of_pos_of_lt_pi (mul_pos hsqrt hx) (hsph h1)) hsqrt
  · have hsqrt : 0 < Real.sqrt (-κ) := Real.sqrt_pos.mpr (by linarith)
    exact div_pos (sinh_pos_of_pos (mul_pos hsqrt hx)) hsqrt
  · exact hx

/-- **Unified curvature-κ Ceva's Theorem.** For any curvature `κ`, the cevians of a
    geodesic triangle are concurrent iff the curvature-sine product of the six sub-segments
    equals `1`. This instantiates the parent's `ceva_unified_principle` at `ρ = sin_κ`,
    subsuming the spherical (κ > 0), hyperbolic (κ < 0), and Euclidean (κ = 0) theorems in a
    single statement. -/
theorem kappa_ceva (κ bd dc ce ea af fb : ℝ)
    (hbd : 0 < sinKappa κ bd) (hdc : 0 < sinKappa κ dc)
    (hce : 0 < sinKappa κ ce) (hea : 0 < sinKappa κ ea)
    (haf : 0 < sinKappa κ af) (hfb : 0 < sinKappa κ fb) :
    sinKappa κ bd / sinKappa κ dc * (sinKappa κ ce / sinKappa κ ea) *
        (sinKappa κ af / sinKappa κ fb) = 1 ↔
    sinKappa κ bd * sinKappa κ ce * sinKappa κ af =
        sinKappa κ dc * sinKappa κ ea * sinKappa κ fb :=
  ceva_unified_principle (sinKappa κ) bd dc ce ea af fb hbd hdc hce hea haf hfb

/-- **Spherical case (κ = 1).** The unified theorem specializes to the classical spherical
    Ceva condition in the ordinary sine. -/
theorem kappa_ceva_spherical (bd dc ce ea af fb : ℝ)
    (hbd : 0 < Real.sin bd) (hdc : 0 < Real.sin dc)
    (hce : 0 < Real.sin ce) (hea : 0 < Real.sin ea)
    (haf : 0 < Real.sin af) (hfb : 0 < Real.sin fb) :
    Real.sin bd / Real.sin dc * (Real.sin ce / Real.sin ea) *
        (Real.sin af / Real.sin fb) = 1 ↔
    Real.sin bd * Real.sin ce * Real.sin af = Real.sin dc * Real.sin ea * Real.sin fb := by
  have := kappa_ceva 1 bd dc ce ea af fb
  simp only [sinKappa_one] at this
  exact this hbd hdc hce hea haf hfb

/-- **Hyperbolic case (κ = −1).** The unified theorem specializes to the hyperbolic Ceva
    condition in the hyperbolic sine. -/
theorem kappa_ceva_hyperbolic (bd dc ce ea af fb : ℝ)
    (hbd : 0 < Real.sinh bd) (hdc : 0 < Real.sinh dc)
    (hce : 0 < Real.sinh ce) (hea : 0 < Real.sinh ea)
    (haf : 0 < Real.sinh af) (hfb : 0 < Real.sinh fb) :
    Real.sinh bd / Real.sinh dc * (Real.sinh ce / Real.sinh ea) *
        (Real.sinh af / Real.sinh fb) = 1 ↔
    Real.sinh bd * Real.sinh ce * Real.sinh af =
        Real.sinh dc * Real.sinh ea * Real.sinh fb := by
  have := kappa_ceva (-1) bd dc ce ea af fb
  simp only [sinKappa_neg_one] at this
  exact this hbd hdc hce hea haf hfb

/-- **Euclidean case (κ = 0).** The unified theorem specializes to the classical Ceva
    condition in plain segment lengths. -/
theorem kappa_ceva_euclidean (bd dc ce ea af fb : ℝ)
    (hbd : 0 < bd) (hdc : 0 < dc) (hce : 0 < ce)
    (hea : 0 < ea) (haf : 0 < af) (hfb : 0 < fb) :
    bd / dc * (ce / ea) * (af / fb) = 1 ↔ bd * ce * af = dc * ea * fb := by
  have := kappa_ceva 0 bd dc ce ea af fb
  simp only [sinKappa_zero] at this
  exact this hbd hdc hce hea haf hfb

end CevasNonEuclideanOQ01
