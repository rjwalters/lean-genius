/-
  The equality (rigidity) case of Wirtinger's inequality — the analytic heart of
  the isoperimetric rigidity theorem "`C² = 4πA` ⟺ the curve is a circle".

  Open Question: area-of-circle-oq-01-oq-02-oq-02-oq-01-oq-01-oq-01

  ## Context

  The parent chain `AreaOfCircleOQ01OQ02OQ02OQ01OQ01*` proves the isoperimetric
  *inequality* `C² ≥ 4πA` (Hurwitz's Fourier proof), with all five analytic
  axioms discharged 0-axiom in sibling files (IFT, Cauchy–Schwarz, Fourier).  The
  inequality reduces, coordinate by coordinate, to **Wirtinger's inequality**

      `∫₀²π f² ≤ ∫₀²π (f')²`     (mean-zero, `2π`-periodic `C¹` `f`).

  This file proves the *equality case*.  Writing `f` in its real Fourier series
  `Σ cₙ`, Parseval gives `∫f² = Σ cₙ²` and `∫(f')² = Σ n²cₙ²`, so

      `∫(f')² − ∫f² = Σ (n² − 1) cₙ²`,

  a sum of **non-negative** terms (using `c₀ = 0` from zero mean).  Hence equality
  holds **iff** every term vanishes, i.e. `cₙ = 0` for all `|n| ≥ 2`: the
  extremiser is a pure *first harmonic* `f(t) = a cos t + b sin t`.  Geometrically,
  forcing this in both coordinates of a constant-speed curve yields a circle —
  the isoperimetric extremiser.

  ## What is proved (all 0-axiom)

  * `wirtinger_inequality`              — `∫f² ≤ ∫(f')²` (context; from the parent
                                          Fourier decomposition).
  * `wirtinger_equality_iff_first_harmonic`
                                        — **the rigidity theorem**: equality holds
                                          iff the Fourier support is `{−1, +1}`.
  * `first_harmonic_mean_zero`,
    `first_harmonic_sq_integral`,
    `first_harmonic_wirtinger_equality` — the concrete extremiser
                                          `a cos t + b sin t`: it has zero mean,
                                          `∫f² = π(a²+b²)`, and **achieves**
                                          Wirtinger equality.

  The heavy Parseval/IBP analytic content is reused verbatim as the proved,
  axiom-free `IsoperimetricOQ.fourier_decomposition` in the grandparent file
  `AreaOfCircleOQ01OQ03.lean`.

  ## Sorries: 0   Axioms: 0
-/
import Mathlib
import Proofs.AreaOfCircleOQ01OQ03

open Real MeasureTheory intervalIntegral

namespace IsoperimetricWirtingerEquality

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

/-- Every `2π`-periodic `C¹` function admits a Fourier decomposition.  The data is
    provided verbatim by `IsoperimetricOQ.fourier_decomposition`. -/
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

/-- **Wirtinger's inequality** (context).  For a mean-zero `2π`-periodic `C¹`
    function, `∫₀²π f² ≤ ∫₀²π (f')²`.

    From the decomposition `c₀ = 0` (mean zero), and for `n ≠ 0`, `n² ≥ 1` gives
    `n²cₙ² ≥ cₙ²`; summing via Parseval yields the claim. -/
theorem wirtinger_inequality (f : ℝ → ℝ) (D : FourierDecomp f)
    (hmean : ∫ t in (0 : ℝ)..(2 * π), f t = 0) :
    ∫ t in (0 : ℝ)..(2 * π), f t ^ 2 ≤
    ∫ t in (0 : ℝ)..(2 * π), deriv f t ^ 2 := by
  have hc0 : D.c 0 = 0 := by rw [D.c_zero, hmean, mul_zero]
  have h_pw : ∀ n : ℤ, D.c n ^ 2 ≤ (↑n : ℝ) ^ 2 * D.c n ^ 2 := by
    intro n
    by_cases hn : n = 0
    · subst hn; rw [hc0]; simp
    · have habs : (1 : ℝ) ≤ |(↑n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
      have h1 : (1 : ℝ) ≤ (↑n : ℝ) ^ 2 := by nlinarith [sq_abs (↑n : ℝ)]
      calc D.c n ^ 2 = 1 * D.c n ^ 2 := (one_mul _).symm
        _ ≤ (↑n : ℝ) ^ 2 * D.c n ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  rw [D.parseval_f, D.parseval_df]
  exact hasSum_le h_pw D.summable_sq.hasSum D.summable_n2_sq.hasSum

/-- **Rigidity / equality case of Wirtinger's inequality.**

    For a mean-zero `2π`-periodic `C¹` function `f` with Fourier decomposition `D`,
    equality `∫f² = ∫(f')²` holds **iff** all Fourier coefficients outside the
    first harmonic vanish (`cₙ = 0` for `n ≠ ±1`).  In other words, the equality
    extremisers are exactly the first harmonics `a cos t + b sin t`. -/
theorem wirtinger_equality_iff_first_harmonic (f : ℝ → ℝ) (D : FourierDecomp f)
    (hmean : ∫ t in (0 : ℝ)..(2 * π), f t = 0) :
    (∫ t in (0 : ℝ)..(2 * π), f t ^ 2 = ∫ t in (0 : ℝ)..(2 * π), deriv f t ^ 2)
      ↔ (∀ n : ℤ, n ≠ 1 → n ≠ -1 → D.c n = 0) := by
  have hc0 : D.c 0 = 0 := by rw [D.c_zero, hmean, mul_zero]
  constructor
  · -- Forward: equality forces the support to be `{−1, +1}`.
    intro hEq n hn1 hn1'
    by_contra hcn
    -- `g n = n²cₙ² − cₙ² = (n²−1)cₙ²`, a non-negative summable family with sum 0.
    set g : ℤ → ℝ := fun m => (↑m : ℝ) ^ 2 * D.c m ^ 2 - D.c m ^ 2 with hg
    have hg_summable : Summable g := by
      rw [hg]; exact D.summable_n2_sq.sub D.summable_sq
    have hg_nonneg : ∀ m : ℤ, 0 ≤ g m := by
      intro m
      simp only [hg]
      by_cases hm : m = 0
      · subst hm; rw [hc0]; norm_num
      · have habs : (1 : ℝ) ≤ |(↑m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
        have h1 : (1 : ℝ) ≤ (↑m : ℝ) ^ 2 := by nlinarith [sq_abs (↑m : ℝ)]
        nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sq_nonneg (D.c m))]
    have hg_tsum : ∑' m, g m = 0 := by
      rw [hg, Summable.tsum_sub D.summable_n2_sq D.summable_sq,
        ← D.parseval_df, ← D.parseval_f]
      linarith [hEq]
    -- But `g n > 0`: from `n ∉ {−1, 0, 1}` we get `n² ≥ 2`, and `cₙ ≠ 0`.
    have hn0 : n ≠ 0 := by rintro rfl; exact hcn hc0
    have hkey : (2 : ℤ) ≤ n ^ 2 := by
      have h2 : n ≤ -2 ∨ 2 ≤ n := by omega
      rcases h2 with h | h
      · nlinarith [sq_nonneg (n + 2)]
      · nlinarith [sq_nonneg (n - 2)]
    have hsqR : (1 : ℝ) < (↑n : ℝ) ^ 2 := by
      have hc : ((2 : ℤ) : ℝ) ≤ ((n ^ 2 : ℤ) : ℝ) := by exact_mod_cast hkey
      push_cast at hc; linarith
    have hcsq : 0 < D.c n ^ 2 := by
      rcases (sq_nonneg (D.c n)).lt_or_eq with h | h
      · exact h
      · exact absurd (sq_eq_zero_iff.mp h.symm) hcn
    have hgn_pos : 0 < g n := by
      rw [hg]; nlinarith [mul_pos (by linarith : (0 : ℝ) < (↑n : ℝ) ^ 2 - 1) hcsq]
    have := Summable.tsum_pos hg_summable hg_nonneg n hgn_pos
    linarith [hg_tsum]
  · -- Backward: support `{−1, +1}` makes the two Parseval sums agree term-by-term.
    intro hsupp
    rw [D.parseval_f, D.parseval_df]
    have hfun : (fun n : ℤ => D.c n ^ 2) = (fun n : ℤ => (↑n : ℝ) ^ 2 * D.c n ^ 2) := by
      funext n
      by_cases h1 : n = 1
      · subst h1; push_cast; ring
      · by_cases h1' : n = -1
        · subst h1'; push_cast; ring
        · rw [hsupp n h1 h1']; ring
    rw [hfun]

/-! ### The concrete extremiser `f(t) = a cos t + b sin t` -/

/-- The derivative of a first harmonic is again a first harmonic. -/
theorem first_harmonic_deriv (a b t : ℝ) :
    deriv (fun s => a * Real.cos s + b * Real.sin s) t
      = -(a * Real.sin t) + b * Real.cos t := by
  have h : HasDerivAt (fun s => a * Real.cos s + b * Real.sin s)
      (a * (-Real.sin t) + b * Real.cos t) t :=
    ((Real.hasDerivAt_cos t).const_mul a).add ((Real.hasDerivAt_sin t).const_mul b)
  rw [h.deriv]; ring

/-- A first harmonic has zero mean over a full period. -/
theorem first_harmonic_mean_zero (a b : ℝ) :
    ∫ t in (0 : ℝ)..(2 * π), (a * Real.cos t + b * Real.sin t) = 0 := by
  rw [intervalIntegral.integral_add
        ((continuous_const.mul Real.continuous_cos).intervalIntegrable _ _)
        ((continuous_const.mul Real.continuous_sin).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_cos, integral_sin]
  simp [Real.cos_zero, Real.sin_zero, Real.cos_two_pi, Real.sin_two_pi]

/-- `∫₀²π (a cos t + b sin t)² = π (a² + b²)`. -/
theorem first_harmonic_sq_integral (a b : ℝ) :
    ∫ t in (0 : ℝ)..(2 * π), (a * Real.cos t + b * Real.sin t) ^ 2
      = π * (a ^ 2 + b ^ 2) := by
  have I1 : IntervalIntegrable (fun t => a ^ 2 * Real.cos t ^ 2) volume 0 (2 * π) :=
    (continuous_const.mul (Real.continuous_cos.pow 2)).intervalIntegrable _ _
  have I2 : IntervalIntegrable
      (fun t => 2 * a * b * (Real.sin t * Real.cos t)) volume 0 (2 * π) :=
    (continuous_const.mul (Real.continuous_sin.mul Real.continuous_cos)).intervalIntegrable _ _
  have I3 : IntervalIntegrable (fun t => b ^ 2 * Real.sin t ^ 2) volume 0 (2 * π) :=
    (continuous_const.mul (Real.continuous_sin.pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr
        (g := fun t => a ^ 2 * Real.cos t ^ 2 + 2 * a * b * (Real.sin t * Real.cos t)
                + b ^ 2 * Real.sin t ^ 2)
        (fun t _ => by ring),
      intervalIntegral.integral_add (I1.add I2) I3,
      intervalIntegral.integral_add I1 I2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      integral_cos_sq, integral_sin_mul_cos₁, integral_sin_sq]
  simp only [Real.cos_zero, Real.sin_zero, Real.cos_two_pi, Real.sin_two_pi]
  ring

/-- **The first harmonic achieves Wirtinger equality.**  For `f(t) = a cos t +
    b sin t`, `∫f² = ∫(f')² = π(a²+b²)`, so the rigidity bound is attained. -/
theorem first_harmonic_wirtinger_equality (a b : ℝ) :
    ∫ t in (0 : ℝ)..(2 * π), (a * Real.cos t + b * Real.sin t) ^ 2
      = ∫ t in (0 : ℝ)..(2 * π),
          deriv (fun s => a * Real.cos s + b * Real.sin s) t ^ 2 := by
  rw [first_harmonic_sq_integral a b,
      intervalIntegral.integral_congr
        (g := fun t => (b * Real.cos t + (-a) * Real.sin t) ^ 2)
        (fun t _ => by rw [first_harmonic_deriv a b t]; ring),
      first_harmonic_sq_integral b (-a)]
  ring

end IsoperimetricWirtingerEquality
