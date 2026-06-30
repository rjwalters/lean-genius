/-
  The two Cauchy–Schwarz analytic axioms of the Hurwitz isoperimetric proof,
  discharged 0-axiom: `integral_cauchy_schwarz_sq` and `area_cauchy_schwarz_bound`.

  Open Question: area-of-circle-oq-01-oq-02-oq-02-oq-01-oq-01

  ## Context

  The parent entry `AreaOfCircleOQ01OQ02OQ02OQ01.lean`
  (`namespace IsoperimetricFromFourier`) proves the isoperimetric inequality
  `C² ≥ 4πA` from five disclosed axioms.  Prior sessions discharged the central
  reparametrization axiom (`exists_nice_reparam`) for regular curves via the
  inverse function theorem (`…OQ01OQ01IFT.lean` / `…OQ01OQ01Reparam.lean`).  The
  four *remaining* parent axioms are the analytic bounds

  * `fourier_decomp_exists`     — Parseval + integration by parts;
  * `wirtinger_sum_bound`       — Wirtinger applied to the coordinates;
  * `area_cauchy_schwarz_bound` — Green's theorem + pointwise 2D Cauchy–Schwarz;
  * `integral_cauchy_schwarz_sq`— L² Cauchy–Schwarz of `1` against `√(x²+y²)`.

  **This file discharges the two Cauchy–Schwarz axioms 0-axiom**, leaving only the
  two genuinely Fourier-analytic axioms.  Both are pure integral inequalities that
  need no Fourier machinery — only continuity of the coordinate functions, which a
  `SmoothClosedCurve` supplies.

  ## Results (namespace `IsoperimetricCauchySchwarz`)

  * `integral_cauchy_schwarz_sq` — for continuous `x, y`,
        `(∫₀²π √(x²+y²))² ≤ 2π · ∫₀²π (x²+y²)`.
    This is the parent axiom verbatim (the axiom imposes no extra hypotheses
    because `SmoothClosedCurve` is `C¹`, hence continuous).  Proved by the
    discriminant of the nonnegative quadratic `λ ↦ ∫₀²π (√(x²+y²) − λ)²`.

  * `area_cauchy_schwarz_bound` — for continuous coordinates `x, y` and continuous
    velocity field `dx, dy` with constant speed `dx² + dy² = c²` (`0 ≤ c`),
        `|∫₀²π (x·dy − y·dx)| ≤ c · ∫₀²π √(x²+y²)`.
    Since the signed area is `A = ½|∫₀²π (x·dy − y·dx)|`, the left side is exactly
    `2A`, so this is the parent axiom `2A ≤ c·∫√(x²+y²)`.  Proved from the
    pointwise 2D Cauchy–Schwarz `|x·dy − y·dx| ≤ √(x²+y²)·√(dx²+dy²)` and
    `√(dx²+dy²) = √(c²) = c`.

  * `area_cauchy_schwarz_bound_contDiff` — the same with `dx, dy` instantiated at
    the actual derivatives `deriv x, deriv y` of `C¹` coordinates: literally the
    shape of the parent axiom `area_cauchy_schwarz_bound`.

  ## Why this does not by itself remove the parent axioms

  These theorems are stated for raw continuous functions, not the parent's
  `SmoothClosedCurve` structure, so wiring them into the parent (to drop its
  `axiomCount`) is a separate, sensitive parent edit.  Mathematically the two
  Cauchy–Schwarz axioms are now fully proved.

  ## Sorries: 0   Axioms: 0
-/
import Mathlib

open Real MeasureTheory intervalIntegral

namespace IsoperimetricCauchySchwarz

/-- **L² Cauchy–Schwarz on `[0, 2π]`** — the parent axiom `integral_cauchy_schwarz_sq`.

For continuous coordinate functions `x, y`,
`(∫₀²π √(x²+y²))² ≤ 2π · ∫₀²π (x²+y²)`.

This is Cauchy–Schwarz of the constant `1` against `g = √(x²+y²)`:
`(∫ 1·g)² ≤ (∫ 1²)(∫ g²) = 2π · ∫ g²`.  We prove it from the discriminant of the
nonnegative quadratic `λ ↦ ∫₀²π (g − λ)² = ∫g² − 2λ∫g + 2π·λ²`, evaluated at
`λ = (∫g)/(2π)`. -/
theorem integral_cauchy_schwarz_sq (x y : ℝ → ℝ)
    (hx : Continuous x) (hy : Continuous y) :
    (∫ t in (0 : ℝ)..(2 * π), √(x t ^ 2 + y t ^ 2)) ^ 2 ≤
      2 * π * ∫ t in (0 : ℝ)..(2 * π), (x t ^ 2 + y t ^ 2) := by
  set g : ℝ → ℝ := fun t => √(x t ^ 2 + y t ^ 2) with hg
  -- continuity / integrability of `g` and `g²`
  have hgc : Continuous g := ((hx.pow 2).add (hy.pow 2)).sqrt
  have hgI : IntervalIntegrable g volume 0 (2 * π) := hgc.intervalIntegrable 0 (2 * π)
  have hg2I : IntervalIntegrable (fun t => g t ^ 2) volume 0 (2 * π) :=
    (hgc.pow 2).intervalIntegrable 0 (2 * π)
  have hconstI : ∀ lam : ℝ, IntervalIntegrable (fun _ : ℝ => lam) volume 0 (2 * π) :=
    fun lam => (continuous_const).intervalIntegrable 0 (2 * π)
  -- `g t ² = x t ² + y t ²`
  have hg2eq : ∀ t, g t ^ 2 = x t ^ 2 + y t ^ 2 := by
    intro t
    have ht : g t = √(x t ^ 2 + y t ^ 2) := by rw [hg]
    rw [ht]; exact Real.sq_sqrt (by positivity)
  -- rewrite the right-hand integrand `x²+y²` as `g²`
  have hRHS : (∫ t in (0 : ℝ)..(2 * π), (x t ^ 2 + y t ^ 2)) =
      ∫ t in (0 : ℝ)..(2 * π), g t ^ 2 := by
    apply integral_congr; intro t _; exact (hg2eq t).symm
  rw [hRHS]
  -- the quadratic in `λ`
  have hpiPos : (0 : ℝ) < 2 * π := by positivity
  have key : ∀ lam : ℝ, (0 : ℝ) ≤ ∫ t in (0 : ℝ)..(2 * π), (g t - lam) ^ 2 := by
    intro lam
    apply intervalIntegral.integral_nonneg (le_of_lt hpiPos)
    intro t _; positivity
  have expand : ∀ lam : ℝ,
      (∫ t in (0 : ℝ)..(2 * π), (g t - lam) ^ 2) =
        (∫ t in (0 : ℝ)..(2 * π), g t ^ 2) - 2 * lam * (∫ t in (0 : ℝ)..(2 * π), g t) +
          lam ^ 2 * (2 * π) := by
    intro lam
    have hcongr : (∫ t in (0 : ℝ)..(2 * π), (g t - lam) ^ 2) =
        ∫ t in (0 : ℝ)..(2 * π), ((g t ^ 2 - (2 * lam) * g t) + lam ^ 2) := by
      apply integral_congr; intro t _; ring
    rw [hcongr,
        integral_add (hg2I.sub (hgI.const_mul (2 * lam))) (hconstI (lam ^ 2)),
        integral_sub hg2I (hgI.const_mul (2 * lam)),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    simp only [smul_eq_mul, sub_zero]
    ring
  -- discriminant: evaluate at `λ = (∫g)/(2π)`
  have hquad : ∀ lam : ℝ,
      (0 : ℝ) ≤ (∫ t in (0 : ℝ)..(2 * π), g t ^ 2) - 2 * lam * (∫ t in (0 : ℝ)..(2 * π), g t) +
        lam ^ 2 * (2 * π) := by
    intro lam; rw [← expand lam]; exact key lam
  set A := ∫ t in (0 : ℝ)..(2 * π), g t ^ 2 with hA
  set B := ∫ t in (0 : ℝ)..(2 * π), g t with hB
  -- goal is now `B^2 ≤ 2π * A`
  have hpiNe : π ≠ 0 := ne_of_gt pi_pos
  have h := hquad (B / (2 * π))
  have hsub : A - 2 * (B / (2 * π)) * B + (B / (2 * π)) ^ 2 * (2 * π) = A - B ^ 2 / (2 * π) := by
    field_simp; ring
  rw [hsub] at h
  have hle : B ^ 2 / (2 * π) ≤ A := by linarith
  calc B ^ 2 = B ^ 2 / (2 * π) * (2 * π) := by field_simp
    _ ≤ A * (2 * π) := by exact mul_le_mul_of_nonneg_right hle (le_of_lt hpiPos)
    _ = 2 * π * A := by ring

/-- **Pointwise 2D Cauchy–Schwarz**: `(a·v − b·u)² ≤ (a²+b²)(u²+v²)`. -/
theorem cross_product_sq_le (a b u v : ℝ) :
    (a * v - b * u) ^ 2 ≤ (a ^ 2 + b ^ 2) * (u ^ 2 + v ^ 2) := by
  nlinarith [sq_nonneg (a * u + b * v)]

/-- **Area bound from Cauchy–Schwarz** — the parent axiom `area_cauchy_schwarz_bound`.

For continuous coordinates `x, y` and a continuous velocity field `dx, dy` of
constant speed `dx² + dy² = c²` with `0 ≤ c`,
`|∫₀²π (x·dy − y·dx)| ≤ c · ∫₀²π √(x²+y²)`.

Since the Green's-theorem signed area is `A = ½|∫₀²π (x·dy − y·dx)|`, the left side
is `2A`, so this is exactly `2A ≤ c · ∫√(x²+y²)`.  Proof: pointwise
`|x·dy − y·dx| ≤ √(x²+y²)·√(dx²+dy²) = c·√(x²+y²)`, then integrate. -/
theorem area_cauchy_schwarz_bound (x y dx dy : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hx : Continuous x) (hy : Continuous y) (hdx : Continuous dx) (hdy : Continuous dy)
    (hspeed : ∀ t, dx t ^ 2 + dy t ^ 2 = c ^ 2) :
    |∫ t in (0 : ℝ)..(2 * π), (x t * dy t - y t * dx t)| ≤
      c * ∫ t in (0 : ℝ)..(2 * π), √(x t ^ 2 + y t ^ 2) := by
  have hpi : (0 : ℝ) ≤ 2 * π := by positivity
  -- pointwise bound on `[0, 2π]`
  have hpw : ∀ t ∈ Set.Icc (0 : ℝ) (2 * π),
      |x t * dy t - y t * dx t| ≤ c * √(x t ^ 2 + y t ^ 2) := by
    intro t _
    have hcs : (x t * dy t - y t * dx t) ^ 2 ≤
        (x t ^ 2 + y t ^ 2) * (dx t ^ 2 + dy t ^ 2) := cross_product_sq_le _ _ _ _
    have h1 : |x t * dy t - y t * dx t| ≤ √((x t ^ 2 + y t ^ 2) * (dx t ^ 2 + dy t ^ 2)) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt hcs
    rw [Real.sqrt_mul (by positivity), hspeed t, Real.sqrt_sq hc] at h1
    rw [mul_comm (√(x t ^ 2 + y t ^ 2)) c] at h1
    exact h1
  -- integrability of the two integrands
  have hI_abs : IntervalIntegrable (fun t => |x t * dy t - y t * dx t|) volume 0 (2 * π) :=
    (((hx.mul hdy).sub (hy.mul hdx)).abs).intervalIntegrable 0 (2 * π)
  have hI_rhs : IntervalIntegrable (fun t => c * √(x t ^ 2 + y t ^ 2)) volume 0 (2 * π) :=
    (continuous_const.mul (((hx.pow 2).add (hy.pow 2)).sqrt)).intervalIntegrable 0 (2 * π)
  -- |∫| ≤ ∫|·| ≤ ∫ c√(x²+y²) = c·∫√(x²+y²)
  have step1 : |∫ t in (0 : ℝ)..(2 * π), (x t * dy t - y t * dx t)| ≤
      ∫ t in (0 : ℝ)..(2 * π), |x t * dy t - y t * dx t| :=
    abs_integral_le_integral_abs hpi
  have step2 : (∫ t in (0 : ℝ)..(2 * π), |x t * dy t - y t * dx t|) ≤
      ∫ t in (0 : ℝ)..(2 * π), c * √(x t ^ 2 + y t ^ 2) :=
    integral_mono_on hpi hI_abs hI_rhs hpw
  have step3 : (∫ t in (0 : ℝ)..(2 * π), c * √(x t ^ 2 + y t ^ 2)) =
      c * ∫ t in (0 : ℝ)..(2 * π), √(x t ^ 2 + y t ^ 2) :=
    intervalIntegral.integral_const_mul c _
  linarith [step1, step2, step3]

/-- The area bound with the velocity field instantiated at the genuine derivatives
of `C¹` coordinates — literally the shape of the parent axiom. -/
theorem area_cauchy_schwarz_bound_contDiff (x y : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hx : ContDiff ℝ 1 x) (hy : ContDiff ℝ 1 y)
    (hspeed : ∀ t, deriv x t ^ 2 + deriv y t ^ 2 = c ^ 2) :
    |∫ t in (0 : ℝ)..(2 * π), (x t * deriv y t - y t * deriv x t)| ≤
      c * ∫ t in (0 : ℝ)..(2 * π), √(x t ^ 2 + y t ^ 2) :=
  area_cauchy_schwarz_bound x y (deriv x) (deriv y) c hc
    hx.continuous hy.continuous hx.continuous_deriv_one hy.continuous_deriv_one hspeed

end IsoperimetricCauchySchwarz
