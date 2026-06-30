/-
  The two Fourier-analytic axioms of the Hurwitz isoperimetric proof,
  discharged 0-axiom: `fourier_decomp_exists` and `wirtinger_sum_bound`.

  Open Question: area-of-circle-oq-01-oq-02-oq-02-oq-01-oq-01

  ## Context

  The parent entry `AreaOfCircleOQ01OQ02OQ02OQ01.lean`
  (`namespace IsoperimetricFromFourier`) proves the isoperimetric inequality
  `C² ≥ 4πA` from five disclosed axioms.  Prior sessions discharged

  * `exists_nice_reparam`      — inverse function theorem (`…OQ01OQ01IFT.lean`);
  * `area_cauchy_schwarz_bound`— Green's theorem + 2D Cauchy–Schwarz (`…CauchySchwarz.lean`);
  * `integral_cauchy_schwarz_sq`— L² Cauchy–Schwarz (`…CauchySchwarz.lean`).

  The two *remaining* parent axioms are the genuinely Fourier-analytic ones:

  * `fourier_decomp_exists` — every `2π`-periodic `C¹` function admits a real
        Fourier decomposition satisfying Parseval for `f` and `f'`;
  * `wirtinger_sum_bound`   — for a zero-mean constant-speed curve,
        `∫₀²π (x²+y²) ≤ 2π c²`.

  **This file discharges both, 0-axiom.**  The heavy analytic content (Parseval
  via `tsum_sq_fourierCoeff` on `AddCircle (2π)`, integration by parts for the
  derivative coefficients) is already a fully proved, axiom-free theorem,
  `IsoperimetricOQ.fourier_decomposition`, in the sibling file
  `AreaOfCircleOQ01OQ03.lean`.  We import it and:

  1. package its existential output into the parent's `FourierDecomp` structure
     (→ `fourier_decomp_exists`);
  2. reprove Wirtinger's inequality for a single coordinate from that
     decomposition (`c₀ = 0` from zero mean, `n² ≥ 1` for `n ≠ 0`);
  3. apply Wirtinger to the two coordinates and integrate the constant-speed
     identity `x'² + y'² = c²` to obtain `wirtinger_sum_bound`.

  With this file the five analytic axioms of the parent isoperimetric proof are
  now *all* discharged as standalone 0-axiom theorems.

  ## Why this does not by itself remove the parent axioms

  As with the Cauchy–Schwarz discharge, `wirtinger_sum_bound` here is stated for
  raw `C¹` periodic coordinate functions rather than the parent's
  `SmoothClosedCurve` structure, so wiring it into the parent (to drop its
  `axiomCount`) is a separate, sensitive parent edit.  Mathematically both
  Fourier axioms are now fully proved.

  ## Sorries: 0   Axioms: 0
-/
import Mathlib
import Proofs.AreaOfCircleOQ01OQ03

open Real MeasureTheory intervalIntegral

namespace IsoperimetricFourier

/-- A Fourier decomposition of a `2π`-periodic `C¹` function `f` into real
    coefficients `cₙ` satisfying Parseval's identity for both `f` and `f'`.
    (Identical to the parent's `IsoperimetricFromFourier.FourierDecomp`.) -/
structure FourierDecomp (f : ℝ → ℝ) where
  /-- Real Fourier coefficients -/
  c : ℤ → ℝ
  /-- The coefficients are square-summable -/
  summable_sq : Summable (fun n : ℤ => c n ^ 2)
  /-- The weighted coefficients `n²cₙ²` are summable -/
  summable_n2_sq : Summable (fun n : ℤ => (↑n : ℝ) ^ 2 * c n ^ 2)
  /-- Parseval for `f`: `∫f² = Σcₙ²` -/
  parseval_f : ∫ t in (0 : ℝ)..(2 * π), f t ^ 2 = ∑' n : ℤ, c n ^ 2
  /-- Parseval for `f'` (via IBP): `∫(f')² = Σn²cₙ²` -/
  parseval_df : ∫ t in (0 : ℝ)..(2 * π), deriv f t ^ 2 = ∑' n : ℤ, (↑n : ℝ) ^ 2 * c n ^ 2
  /-- The zeroth coefficient captures the mean -/
  c_zero : c 0 = (1 / Real.sqrt (2 * π)) * ∫ t in (0 : ℝ)..(2 * π), f t

/-- **Discharges the parent axiom `fourier_decomp_exists`.**
    Every `2π`-periodic `C¹` function admits a Fourier decomposition.  The data
    is provided verbatim by `IsoperimetricOQ.fourier_decomposition`; we only
    repackage the existential into the structure. -/
theorem fourier_decomp_exists (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t) :
    Nonempty (FourierDecomp f) := by
  obtain ⟨c, hsum, hsum', hf_sq, hdf_sq, hc0⟩ :=
    IsoperimetricOQ.fourier_decomposition f hf hperiod
  exact ⟨{ c := c
           summable_sq := hsum
           summable_n2_sq := hsum'
           parseval_f := hf_sq
           parseval_df := hdf_sq
           c_zero := hc0 }⟩

/-- **Wirtinger's inequality**: for a mean-zero `2π`-periodic `C¹` function,
    `∫₀²π f² ≤ ∫₀²π (f')²`.

    Proof: from the Fourier decomposition, `c₀ = 0` (mean zero), and for `n ≠ 0`,
    `n² ≥ 1` gives `n²cₙ² ≥ cₙ²`; summing via Parseval yields the claim. -/
theorem wirtinger_inequality (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hperiod : ∀ t, f (t + 2 * π) = f t)
    (hmean : ∫ t in (0 : ℝ)..(2 * π), f t = 0) :
    ∫ t in (0 : ℝ)..(2 * π), f t ^ 2 ≤
    ∫ t in (0 : ℝ)..(2 * π), deriv f t ^ 2 := by
  obtain ⟨c, hsum, hsum', hf_sq, hdf_sq, hc0⟩ :=
    IsoperimetricOQ.fourier_decomposition f hf hperiod
  -- c₀ = 0 from zero mean
  have hc0' : c 0 = 0 := by rw [hc0, hmean, mul_zero]
  -- Pointwise bound n²cₙ² ≥ cₙ² for all n
  have h_pw : ∀ n : ℤ, c n ^ 2 ≤ (↑n : ℝ) ^ 2 * c n ^ 2 := by
    intro n
    by_cases hn : n = 0
    · subst hn; rw [hc0']; simp
    · have habs : (1 : ℝ) ≤ |(↑n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      have h1 : (1 : ℝ) ≤ (↑n : ℝ) ^ 2 := by nlinarith [sq_abs (↑n : ℝ)]
      calc c n ^ 2 = 1 * c n ^ 2 := (one_mul _).symm
        _ ≤ (↑n : ℝ) ^ 2 * c n ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  -- Sum the pointwise bounds via Parseval
  rw [hf_sq, hdf_sq]
  exact hasSum_le h_pw hsum.hasSum hsum'.hasSum

/-- **Discharges the parent axiom `wirtinger_sum_bound`.**
    For a zero-mean constant-speed `C¹` closed curve `(x, y)` with speed `c`,
    `∫₀²π (x² + y²) ≤ 2π c²`.

    Proof: apply Wirtinger to `x` and `y` separately, then integrate the
    constant-speed identity `x'² + y'² = c²` over `[0, 2π]`. -/
theorem wirtinger_sum_bound (x y : ℝ → ℝ)
    (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y)
    (hpx : ∀ t, x (t + 2 * π) = x t) (hpy : ∀ t, y (t + 2 * π) = y t)
    (c : ℝ) (hc : 0 < c)
    (hspeed : ∀ t, deriv x t ^ 2 + deriv y t ^ 2 = c ^ 2)
    (hzx : ∫ t in (0 : ℝ)..(2 * π), x t = 0)
    (hzy : ∫ t in (0 : ℝ)..(2 * π), y t = 0) :
    ∫ t in (0 : ℝ)..(2 * π), (x t ^ 2 + y t ^ 2) ≤ 2 * π * c ^ 2 := by
  -- Wirtinger on each coordinate
  have hWx := wirtinger_inequality x hx hpx hzx
  have hWy := wirtinger_inequality y hy hpy hzy
  -- Continuity of coordinates and their derivatives
  have hcx : Continuous x := hx.continuous
  have hcy : Continuous y := hy.continuous
  have hcdx : Continuous (deriv x) := hx.continuous_deriv le_rfl
  have hcdy : Continuous (deriv y) := hy.continuous_deriv le_rfl
  -- Interval integrability of the four squares
  have ix2 : IntervalIntegrable (fun t => x t ^ 2) volume 0 (2 * π) :=
    (hcx.pow 2).intervalIntegrable _ _
  have iy2 : IntervalIntegrable (fun t => y t ^ 2) volume 0 (2 * π) :=
    (hcy.pow 2).intervalIntegrable _ _
  have idx2 : IntervalIntegrable (fun t => deriv x t ^ 2) volume 0 (2 * π) :=
    (hcdx.pow 2).intervalIntegrable _ _
  have idy2 : IntervalIntegrable (fun t => deriv y t ^ 2) volume 0 (2 * π) :=
    (hcdy.pow 2).intervalIntegrable _ _
  -- Split the left-hand integral
  have hsplitL : (∫ t in (0 : ℝ)..(2 * π), (x t ^ 2 + y t ^ 2))
      = (∫ t in (0 : ℝ)..(2 * π), x t ^ 2) + ∫ t in (0 : ℝ)..(2 * π), y t ^ 2 :=
    intervalIntegral.integral_add ix2 iy2
  -- Combine the derivative integrals
  have hcombine : (∫ t in (0 : ℝ)..(2 * π), deriv x t ^ 2)
        + (∫ t in (0 : ℝ)..(2 * π), deriv y t ^ 2)
      = ∫ t in (0 : ℝ)..(2 * π), (deriv x t ^ 2 + deriv y t ^ 2) :=
    (intervalIntegral.integral_add idx2 idy2).symm
  -- Integrate the constant-speed identity: ∫ (x'² + y'²) = ∫ c² = 2π c²
  have heqon : Set.EqOn (fun t => deriv x t ^ 2 + deriv y t ^ 2)
      (fun _ => c ^ 2) (Set.uIcc 0 (2 * π)) := fun t _ => hspeed t
  have hspeed_int : (∫ t in (0 : ℝ)..(2 * π), (deriv x t ^ 2 + deriv y t ^ 2))
      = 2 * π * c ^ 2 := by
    rw [intervalIntegral.integral_congr heqon, intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
  -- Chain the bounds
  rw [hsplitL]
  calc (∫ t in (0 : ℝ)..(2 * π), x t ^ 2) + ∫ t in (0 : ℝ)..(2 * π), y t ^ 2
      ≤ (∫ t in (0 : ℝ)..(2 * π), deriv x t ^ 2)
          + ∫ t in (0 : ℝ)..(2 * π), deriv y t ^ 2 := add_le_add hWx hWy
    _ = ∫ t in (0 : ℝ)..(2 * π), (deriv x t ^ 2 + deriv y t ^ 2) := hcombine
    _ = 2 * π * c ^ 2 := hspeed_int

end IsoperimetricFourier
