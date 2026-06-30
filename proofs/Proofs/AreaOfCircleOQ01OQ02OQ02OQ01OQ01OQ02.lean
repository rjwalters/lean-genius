/-
  The isoperimetric inequality `4πA ≤ L²`, fully axiom-free, for regular closed curves.

  Open Question: area-of-circle-oq-01-oq-02-oq-02-oq-01-oq-01
  (child slug: area-of-circle-oq-01-oq-02-oq-02-oq-01-oq-01-oq-02)

  ## Context — the capstone of the Hurwitz isoperimetric program

  The gallery parent `AreaOfCircleOQ01OQ02OQ02OQ01.lean` (`namespace IsoperimetricFromFourier`)
  proves the isoperimetric inequality `C² ≥ 4πA` for `SmoothClosedCurve`s from **five disclosed
  axioms**:

  1. `fourier_decomp_exists`      — Parseval/IBP Fourier decomposition,
  2. `exists_nice_reparam`        — constant-speed, zero-mean reparametrization (the IFT step),
  3. `wirtinger_sum_bound`        — Wirtinger applied to the coordinate functions,
  4. `area_cauchy_schwarz_bound`  — Green's-formula area ≤ `c·∫√(x²+y²)` (pointwise 2-D CS),
  5. `integral_cauchy_schwarz_sq` — the L² Cauchy–Schwarz `S² ≤ 2π·∫(x²+y²)`,

  together with the *fully proved* `isoperimetric_arithmetic_kernel` (the purely algebraic
  deduction `4πA ≤ L²` from the analytic bounds).

  Across the OQ research lineage each of these five analytic axioms was **individually
  discharged, 0-axiom**, in self-contained companions:

  * `AreaOfCircleOQ01OQ02OQ02OQ01OQ01Fourier.lean` (`namespace IsoperimetricFourier`):
    `fourier_decomp_exists`, `wirtinger_inequality`, and `wirtinger_sum_bound` (#3).
  * `AreaOfCircleOQ01OQ02OQ02OQ01OQ01CauchySchwarz.lean` (`namespace IsoperimetricCauchySchwarz`):
    `integral_cauchy_schwarz_sq` (#5) and `area_cauchy_schwarz_bound_contDiff` (#4).
  * `AreaOfCircleOQ01OQ02OQ02OQ01OQ01IFT.lean` (`namespace RegularCurveArcLength`):
    `exists_nice_reparam_for_regular` (#2) — the inverse-function-theorem arc-length
    reparametrization, proved for the `RegularClosedCurve` structure (the regularity field is
    genuinely needed: the axiom is *false* for curves with stationary points, see that file's
    header, "Gap 1").

  Each companion stood alone. **This file performs the final assembly**: it feeds the four
  discharged analytic bounds (on the constant-speed, zero-mean reparametrization produced by the
  IFT) into the algebraic kernel and obtains the isoperimetric inequality

      `isoperimetric_inequality_regular : 4 * π * γ.area ≤ γ.circumference ^ 2`

  for every `RegularClosedCurve γ` with positive circumference — with **0 axioms and 0 sorries**.

  This is the maximal honest endpoint of the program: the parent's statement quantifies over all
  `SmoothClosedCurve`, where the reparametrization axiom is genuinely false (stationary points),
  so a literal 0-axiom replacement of the parent theorem is impossible. On the regular locus —
  exactly where the inverse-function-theorem route can succeed — the entire chain
  Fourier ⇒ Wirtinger ⇒ Cauchy–Schwarz ⇒ IFT reparametrization ⇒ arithmetic kernel is now
  machine-checked end to end with no remaining assumptions.

  ## Proof

  Mirrors the parent's `isoperimetric_inequality` proof verbatim, but every axiom invocation is
  replaced by the corresponding 0-axiom companion theorem, and the curve structure is
  `RegularClosedCurve` (so the reparametrization actually exists). Given `γ`:

  * `exists_nice_reparam_for_regular` yields a regular curve `ρ` with the same circumference and
    area, constant speed `c = L/(2π)`, and zero mean.
  * `wirtinger_sum_bound` on `(ρ.x, ρ.y)` gives `∫(ρ.x²+ρ.y²) ≤ 2πc²`.
  * `integral_cauchy_schwarz_sq` on `(ρ.x, ρ.y)` gives `S² ≤ 2π·∫(ρ.x²+ρ.y²)`.
  * `area_cauchy_schwarz_bound_contDiff` gives `|∫(ρ.x·ρ.y' − ρ.y·ρ.x')| ≤ c·S`, and since
    `2·ρ.area = |∫(…)|` this is `2·ρ.area ≤ c·S`.
  * `isoperimetric_arithmetic_kernel` assembles these into `4π·ρ.area ≤ ρ.circumference²`, which
    transports back to `γ` by the circumference/area preservation of `ρ`.

  ## Sorries: 0   Axioms: 0
-/
import Mathlib
import Proofs.AreaOfCircleOQ01OQ02OQ02OQ01OQ01Fourier
import Proofs.AreaOfCircleOQ01OQ02OQ02OQ01OQ01CauchySchwarz
import Proofs.AreaOfCircleOQ01OQ02OQ02OQ01OQ01IFT

open Real MeasureTheory intervalIntegral Topology Filter

namespace IsoperimetricCapstone

open RegularCurveArcLength

/-! ### The algebraic kernel

The parent entry's purely-algebraic `isoperimetric_arithmetic_kernel` — re-proved here verbatim
so this capstone is self-contained and does not depend on the (currently Mathlib-v4.26.0
bit-rotted) parent file `AreaOfCircleOQ01OQ02OQ02OQ01.lean`.  No integrals or measures appear;
it is the final algebraic step of Hurwitz's 1901 proof once the analytic bounds are assembled. -/

/-- **Arithmetic kernel**: from the assembled analytic bounds (`2A ≤ cS`, `S² ≤ 2π·Sxy`,
`Sxy ≤ 2πc²`) and `L = 2πc`, deduce `4πA ≤ L²`. Purely algebraic. -/
theorem isoperimetric_arithmetic_kernel
    (A L c S Sxy : ℝ)
    (hc : 0 < c)
    (hcirc : L = 2 * π * c)
    (hS_nn : 0 ≤ S)
    (harea : 2 * A ≤ c * S)
    (hCS : S ^ 2 ≤ 2 * π * Sxy)
    (hWirt : Sxy ≤ 2 * π * c ^ 2) :
    4 * π * A ≤ L ^ 2 := by
  have hpi : (0 : ℝ) < π := pi_pos
  have h2pic_pos : (0 : ℝ) < 2 * π * c := by positivity
  have hS2 : S ^ 2 ≤ (2 * π * c) ^ 2 :=
    calc S ^ 2 ≤ 2 * π * Sxy := hCS
      _ ≤ 2 * π * (2 * π * c ^ 2) := mul_le_mul_of_nonneg_left hWirt (by linarith)
      _ = (2 * π * c) ^ 2 := by ring
  have hS_bound : S ≤ 2 * π * c := by
    have h := Real.sqrt_le_sqrt hS2
    rwa [Real.sqrt_sq hS_nn, Real.sqrt_sq h2pic_pos.le] at h
  have h1 : c * S ≤ 2 * π * c ^ 2 := by nlinarith
  have h2 : 2 * A ≤ 2 * π * c ^ 2 := le_trans harea h1
  calc 4 * π * A = 2 * π * (2 * A) := by ring
    _ ≤ 2 * π * (2 * π * c ^ 2) := mul_le_mul_of_nonneg_left h2 (by linarith)
    _ = (2 * π * c) ^ 2 := by ring
    _ = L ^ 2 := by rw [hcirc]

/-- **The isoperimetric inequality `4πA ≤ L²` for regular closed curves — 0 axioms.**

For every regular `C¹` closed plane curve `γ` (`2π`-periodic, nowhere-vanishing speed) with
positive circumference `L = γ.circumference` and enclosed signed area `A = γ.area`,

  `4 * π * A ≤ L²`.

This is Hurwitz's 1901 isoperimetric inequality, assembled entirely from machine-checked,
axiom-free pieces: the Fourier/Wirtinger bound, the two Cauchy–Schwarz bounds, the
inverse-function-theorem constant-speed reparametrization, and the algebraic kernel. Every one of
the parent entry's five analytic axioms has been discharged; this theorem invokes none of them. -/
theorem isoperimetric_inequality_regular (γ : RegularClosedCurve)
    (hL : 0 < γ.circumference) :
    4 * π * γ.area ≤ γ.circumference ^ 2 := by
  -- Step 1: constant-speed, zero-mean reparametrization (inverse function theorem, 0-axiom).
  obtain ⟨ρ, hρcirc, hρarea, hρspeed, hρzx, hρzy⟩ :=
    RegularClosedCurve.exists_nice_reparam_for_regular γ hL
  -- Step 2: the constant speed `c = L/(2π)`.
  set c := γ.circumference / (2 * π) with hc_def
  have hc_pos : 0 < c := div_pos hL (by positivity)
  -- `set` has folded the speed hypothesis to `… = c²`.
  -- Step 3: name the two integral aggregates `S = ∫√(x²+y²)` and `Sxy = ∫(x²+y²)`.
  set S := ∫ t in (0 : ℝ)..(2 * π), Real.sqrt (ρ.x t ^ 2 + ρ.y t ^ 2) with hS_def
  set Sxy := ∫ t in (0 : ℝ)..(2 * π), (ρ.x t ^ 2 + ρ.y t ^ 2) with hSxy_def
  -- Step 4: `S ≥ 0`.
  have hS_nn : 0 ≤ S := by
    rw [hS_def]
    apply intervalIntegral.integral_nonneg (by positivity)
    intro t _
    exact Real.sqrt_nonneg _
  -- Step 5: the three analytic bounds, each from a 0-axiom companion.
  -- Wirtinger sum bound:  `Sxy ≤ 2πc²`.
  have hWirt : Sxy ≤ 2 * π * c ^ 2 :=
    IsoperimetricFourier.wirtinger_sum_bound ρ.x ρ.y ρ.smooth_x ρ.smooth_y
      ρ.periodic_x ρ.periodic_y c hc_pos hρspeed hρzx hρzy
  -- L² Cauchy–Schwarz:  `S² ≤ 2π·Sxy`.
  have hCS : S ^ 2 ≤ 2 * π * Sxy :=
    IsoperimetricCauchySchwarz.integral_cauchy_schwarz_sq ρ.x ρ.y
      ρ.smooth_x.continuous ρ.smooth_y.continuous
  -- Area Cauchy–Schwarz:  `|∫(x·y' − y·x')| ≤ c·S`, i.e. `2·area ≤ c·S`.
  have hAbs : |∫ t in (0 : ℝ)..(2 * π), (ρ.x t * deriv ρ.y t - ρ.y t * deriv ρ.x t)| ≤ c * S :=
    IsoperimetricCauchySchwarz.area_cauchy_schwarz_bound_contDiff ρ.x ρ.y c hc_pos.le
      ρ.smooth_x ρ.smooth_y hρspeed
  have h2area : 2 * ρ.area =
      |∫ t in (0 : ℝ)..(2 * π), (ρ.x t * deriv ρ.y t - ρ.y t * deriv ρ.x t)| := by
    unfold RegularCurveArcLength.RegularClosedCurve.area
    ring
  have hArea : 2 * ρ.area ≤ c * S := by rw [h2area]; exact hAbs
  -- Step 6: transport the goal to `ρ` and apply the algebraic kernel.
  rw [← hρarea, ← hρcirc]
  exact isoperimetric_arithmetic_kernel
    ρ.area ρ.circumference c S Sxy hc_pos
    (by rw [hρcirc, hc_def]; field_simp) hS_nn hArea hCS hWirt

end IsoperimetricCapstone
