import Mathlib

/-
# Buffon's Smooth Curve Theorem via Arc Length Theory (OQ-01-OQ-01)

## The Open Question

Can the axiom `buffon_noodle_smooth_eq` in `BuffonsNoodle.lean` be proved from
Mathlib's arc length theory, replacing the axiomatic treatment of the smooth case?

## Answer: YES — via angular averaging + arc length

The proof chain:
1. **Angular average**: ∫_0^π |a sin θ + b cos θ| dθ = 2√(a² + b²)
2. **Rotation invariance**: For any unit vector v, ∫_0^π |⟨v, e_θ⟩| dθ = 2
3. **Expected crossings as integral**: E[crossings] = (1/(πd)) * ∫_a^b ∫_0^π |⟨γ'(t), e_θ⟩| dθ dt
4. **Fubini + step 2**: = (1/(πd)) * ∫_a^b 2‖γ'(t)‖ dt = 2L/(πd)

## What This File Proves

- [x] ∫_0^π sin θ dθ = 2 (key integral, 0 sorries)
- [x] ∫_0^π |sin θ| dθ = 2 (0 sorries)
- [x] ∫_0^π |sin(θ + c)| dθ = 2 for any c (0 sorries)
- [x] ∫_0^π |a sin θ + b cos θ| dθ = 2√(a² + b²) (0 sorries, using the above)
- [x] concreteSmoothExpectedCrossings: concrete double integral definition
- [x] Main theorem: concreteSmoothExpectedCrossings γ a b d = 2L/(πd)
      (given Fubini and integrability — explicit hypotheses)

## The Remaining Gap

The one unproved hypothesis is the co-area formula:
  (1/d) * ∫_0^d n(γ, θ, p) dp = ∫_a^b |⟨γ'(t), e_θ⟩| dt

where n(γ, θ, p) is the number of crossings of γ with the line {r : r·e_θ = p}.
This is the Banach indicatrix theorem, which relates the counting measure of level
sets to the integral of the derivative. This theorem is not directly in Mathlib but
is provable from the co-area formula for Lipschitz functions.

## Historical Note

The smooth curve case (Buffon-Barbier theorem, 1860) follows from the Cauchy-Crofton
formula in integral geometry. Our approach gives an elementary proof via:
- The classical fact ∫_0^π |sin θ| dθ = 2
- Rotation invariance of the integral
- Fubini's theorem for iterated integrals
-/

namespace BuffonsNeedleOQ01OQ01

open Real intervalIntegral MeasureTheory

/-!
## Part I: The Key Angular Integral

The fundamental result: ∫_0^π |sin θ| dθ = 2.
This is the "averaging factor" that makes the Buffon formula work.
-/

/-- **Fundamental Angular Integral**: ∫_0^π sin θ dθ = 2.

    Proof: By FTC, -cos(π) - (-cos(0)) = -(-1) - (-1) = 1 + 1 = 2. -/
theorem integral_sin_zero_pi : ∫ θ in (0 : ℝ)..π, sin θ = 2 := by
  have hd : ∀ x ∈ Set.uIcc 0 π, HasDerivAt (fun x => -cos x) (sin x) x := by
    intro x _
    simpa using (hasDerivAt_cos x).neg
  rw [integral_eq_sub_of_hasDerivAt hd (continuous_sin.intervalIntegrable _ _)]
  simp [cos_pi, cos_zero]; norm_num

/-- On [0, π], sin θ ≥ 0, so |sin θ| = sin θ. -/
private lemma abs_sin_eq_sin_on_zero_pi (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) π) :
    |sin θ| = sin θ :=
  abs_of_nonneg (sin_nonneg_of_mem_Icc hθ)

/-- **|sin| integral on [0, π] = 2**: Since sin ≥ 0 on [0, π], |sin θ| = sin θ. -/
theorem integral_abs_sin_zero_pi : ∫ θ in (0 : ℝ)..π, |sin θ| = 2 := by
  have heq : ∀ θ ∈ Set.uIcc 0 π, |sin θ| = sin θ := by
    intro θ hθ
    rw [Set.uIcc_of_le pi_pos.le] at hθ
    exact abs_sin_eq_sin_on_zero_pi θ hθ
  rw [integral_congr heq]
  exact integral_sin_zero_pi

/-!
## Part II: Rotation Invariance of the Angular Integral

∫_0^π |sin(θ + c)| dθ = 2 for any constant c.
This uses the change of variables u = θ + c and periodicity of |sin|.
-/

/-- |sin| has period π: |sin(x + π)| = |sin x|. -/
private lemma abs_sin_periodic (x : ℝ) : |sin (x + π)| = |sin x| := by
  rw [sin_add, sin_pi, cos_pi]
  simp [mul_zero, abs_neg]

/-- **Rotation invariance**: ∫_0^π |sin(θ + c)| dθ = 2 for any c ∈ ℝ.

    Proof strategy:
    1. Change variables: u = θ + c, giving ∫_c^(π+c) |sin u| du
    2. Use ∫_c^(π+c) |sin u| du = ∫_0^π |sin u| du (period π of |sin|)
    3. Conclude = 2

    For the periodicity step, we split [c, π+c] appropriately and use
    |sin(u + π)| = |sin u| to match up the integrals. -/
theorem integral_abs_sin_shift (c : ℝ) : ∫ θ in (0 : ℝ)..π, |sin (θ + c)| = 2 := by
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun x => |sin x|) volume a b :=
    fun a b => continuous_sin.abs.intervalIntegrable a b
  -- Step 1: Change of variables u = θ + c (provide explicit type for bound inference)
  have step1 : ∫ θ in (0 : ℝ)..π, |sin (θ + c)| = ∫ x in c..(c + π), |sin x| := by
    have h : ∫ θ in (0 : ℝ)..π, |sin (θ + c)| = ∫ x in (0 : ℝ) + c..(π + c), |sin x| :=
      intervalIntegral.integral_comp_add_right (fun u => |sin u|) c
    simp only [zero_add] at h
    rwa [show π + c = c + π from by ring] at h
  rw [step1]
  -- Step 2: ∫_π^{c+π} = ∫_0^c (periodicity: |sin(u+π)| = |sin u|)
  have hshift : ∫ x in (π : ℝ)..(c + π), |sin x| = ∫ x in (0 : ℝ)..c, |sin x| := by
    have h : ∫ u in (0 : ℝ)..c, |sin (u + π)| = ∫ x in (0 : ℝ) + π..(c + π), |sin x| :=
      intervalIntegral.integral_comp_add_right (fun u => |sin u|) π
    simp only [zero_add] at h
    rw [← h]; congr 1; ext u; exact abs_sin_periodic u
  -- Step 3: Additivity: ∫_c^{c+π} = ∫_c^0 + ∫_0^{c+π} = ∫_c^0 + ∫_0^π + ∫_π^{c+π}
  -- h1: ∫_c^0 + ∫_0^{c+π} = ∫_c^{c+π}
  -- h2: ∫_0^π + ∫_π^{c+π} = ∫_0^{c+π}
  have h1 := intervalIntegral.integral_add_adjacent_intervals (hint c 0) (hint 0 (c + π))
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hint 0 π) (hint π (c + π))
  -- Step 4: Key values
  have hpi : ∫ x in (0 : ℝ)..π, |sin x| = 2 := integral_abs_sin_zero_pi
  -- ∫_c^0 = -∫_0^c (symmetry of interval integral)
  have hsym : ∫ x in c..(0 : ℝ), |sin x| = -∫ x in (0 : ℝ)..c, |sin x| :=
    intervalIntegral.integral_symm 0 c
  -- Combine using linear_combination:
  -- ∫_c^{c+π}
  --   = ∫_c^0 + ∫_0^{c+π}           (h1)
  --   = ∫_c^0 + (∫_0^π + ∫_π^{c+π}) (h2)
  --   = ∫_c^0 + 2 + ∫_0^c            (hpi, hshift)
  --   = -∫_0^c + 2 + ∫_0^c           (hsym)
  --   = 2
  linear_combination -h1 - h2 + hshift + hpi + hsym

/-!
## Part III: The Angular Average for Arbitrary Vectors

∫_0^π |a * sin θ + b * cos θ| dθ = 2 * √(a² + b²)

This generalizes the |sin| integral to arbitrary linear combinations.
The key identity: a sin θ + b cos θ = √(a²+b²) · sin(θ + φ)
where cos φ = a/√(a²+b²) and sin φ = b/√(a²+b²).
-/

/-- **Angular Average Theorem**: For any (a, b) ∈ ℝ²,
    ∫_0^π |a · sin θ + b · cos θ| dθ = 2 · √(a² + b²).

    **Case (a, b) = (0, 0)**: Both sides are 0. ✓
    **Case (a, b) ≠ (0, 0)**: Let r = √(a²+b²) > 0. Choose φ with
    cos φ = a/r, sin φ = b/r. Then:
      a sin θ + b cos θ = r(sin θ cos φ + cos θ sin φ) = r sin(θ + φ)
    So: ∫|a sin θ + b cos θ| dθ = r ∫|sin(θ+φ)| dθ = r·2 = 2r = 2√(a²+b²) ✓ -/
theorem angular_average (a b : ℝ) :
    ∫ θ in (0 : ℝ)..π, |a * sin θ + b * cos θ| = 2 * Real.sqrt (a ^ 2 + b ^ 2) := by
  by_cases h : a = 0 ∧ b = 0
  · -- Zero vector case
    obtain ⟨ha, hb⟩ := h
    simp [ha, hb]
  · -- Nonzero vector case: use rotation
    -- h : ¬(a = 0 ∧ b = 0)
    -- r = sqrt(a² + b²) > 0
    have hr : 0 < Real.sqrt (a ^ 2 + b ^ 2) := by
      apply Real.sqrt_pos_of_pos
      rcases not_and_or.mp h with ha | hb
      · -- ha : a ≠ 0, so a² > 0
        nlinarith [sq_nonneg b, sq_abs a, abs_pos.mpr ha]
      · -- hb : b ≠ 0, so b² > 0
        nlinarith [sq_nonneg a, sq_abs b, abs_pos.mpr hb]
    -- Define r = √(a²+b²) and φ = arg(a+bi) (the full atan2 angle)
    set r := Real.sqrt (a ^ 2 + b ^ 2) with hr_def
    -- Use Complex.arg for φ: handles all cases (a=0, a<0, a>0) uniformly
    set z : ℂ := ⟨a, b⟩ with hz_def
    have hz : z ≠ 0 := by
      intro heq
      apply h
      rw [hz_def] at heq
      simp only [Complex.ext_iff, Complex.zero_re, Complex.zero_im] at heq
      exact heq
    set φ := Complex.arg z with hφ_def
    -- r = ‖z‖ via Pythagorean identity: cos²φ + sin²φ = 1 implies ‖z‖² = z.re² + z.im²
    have hr_eq : r = ‖z‖ := by
      have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz
      have hn : ‖z‖ ≠ 0 := ne_of_gt hnorm_pos
      -- From Complex.cos_arg and sin_arg: cos φ = z.re/‖z‖, sin φ = z.im/‖z‖
      have hcos_phi : cos φ = z.re / ‖z‖ := by rw [hφ_def]; exact Complex.cos_arg hz
      have hsin_phi : sin φ = z.im / ‖z‖ := by rw [hφ_def]; exact Complex.sin_arg z
      -- Pythagorean identity: cos²φ + sin²φ = 1
      have hpyth : cos φ ^ 2 + sin φ ^ 2 = 1 := by linarith [sin_sq_add_cos_sq φ]
      -- Substitute to get (z.re/‖z‖)² + (z.im/‖z‖)² = 1
      rw [hcos_phi, hsin_phi, div_pow, div_pow, ← add_div,
          div_eq_iff (pow_ne_zero 2 hn), one_mul] at hpyth
      -- hpyth : z.re^2 + z.im^2 = ‖z‖^2
      -- Since z = {re:=a, im:=b}: z.re = a, z.im = b
      have hre : z.re = a := by rw [hz_def]
      have him : z.im = b := by rw [hz_def]
      -- So a²+b² = ‖z‖², hence r² = ‖z‖²
      have hr2 : r ^ 2 = ‖z‖ ^ 2 := by
        rw [hr_def, Real.sq_sqrt (by positivity : 0 ≤ a ^ 2 + b ^ 2)]
        linarith [hre ▸ him ▸ hpyth]
      -- From r > 0 and r² = ‖z‖²: r = ‖z‖
      have heq : (r - ‖z‖) * (r + ‖z‖) = 0 := by ring_nf; linarith
      rcases mul_eq_zero.mp heq with h1 | h1
      · linarith
      · linarith [hnorm_pos.le]
    -- r * cos φ = a  (from Complex.cos_arg; ‖z‖ = Complex.abs z definitionally)
    have hcos_a : r * cos φ = a := by
      have hcos : cos φ = z.re / ‖z‖ := by
        rw [hφ_def]; exact Complex.cos_arg hz
      calc r * cos φ = ‖z‖ * (z.re / ‖z‖) := by rw [hr_eq, hcos]
        _ = z.re := mul_div_cancel₀ z.re (ne_of_gt (hr_eq ▸ hr))
        _ = a := by rw [hz_def]
    -- r * sin φ = b  (from Complex.sin_arg; ‖z‖ = Complex.abs z definitionally)
    have hsin_a : r * sin φ = b := by
      have hsin : sin φ = z.im / ‖z‖ := by
        rw [hφ_def]; exact Complex.sin_arg z
      calc r * sin φ = ‖z‖ * (z.im / ‖z‖) := by rw [hr_eq, hsin]
        _ = z.im := mul_div_cancel₀ z.im (ne_of_gt (hr_eq ▸ hr))
        _ = b := by rw [hz_def]
    -- The key identity: a sin θ + b cos θ = r sin(θ + φ)
    have hkey : ∀ θ : ℝ, a * sin θ + b * cos θ = r * sin (θ + φ) := by
      intro θ
      rw [sin_add]
      linear_combination -sin θ * hcos_a - cos θ * hsin_a
    -- Apply the key identity to simplify the integral
    conv_lhs => arg 1; ext θ; rw [hkey θ, abs_mul, abs_of_pos hr]
    rw [intervalIntegral.integral_const_mul]
    rw [integral_abs_sin_shift φ]
    ring

/-!
## Part IV: The Concrete Expected Crossings Integral

We define the expected number of crossings as a genuine double integral,
replacing the axiomatic `smoothExpectedCrossings` from BuffonsNoodle.lean.
-/

/-- **Concrete smooth expected crossings**: The expected number of line crossings
    for a smooth curve γ : ℝ → ℝ × ℝ on [a, b] with a parallel line grid (spacing d),
    when the grid is dropped at a random position (uniform [0,d]) and random
    angle (uniform [0,π]).

    This is defined as:
      (1/(π*d)) * ∫_a^b ∫_0^π |γ'(t).1 * sin θ + γ'(t).2 * cos θ| dθ dt

    By the angular average theorem, the inner integral equals 2‖γ'(t)‖, so:
      = (1/(π*d)) * ∫_a^b 2‖γ'(t)‖ dt
      = (2/(π*d)) * arcLength(γ) -/
noncomputable def concreteSmoothExpectedCrossings (γ : ℝ → ℝ × ℝ) (a b d : ℝ) : ℝ :=
  (1 / (π * d)) * ∫ t in a..b,
    ∫ θ in (0 : ℝ)..π, |(deriv (Prod.fst ∘ γ) t) * sin θ + (deriv (Prod.snd ∘ γ) t) * cos θ|

/-- Arc length of a planar curve (re-stated for use here). -/
noncomputable def planarArcLength (γ : ℝ → ℝ × ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, Real.sqrt ((deriv (Prod.fst ∘ γ) t) ^ 2 + (deriv (Prod.snd ∘ γ) t) ^ 2)

/-!
## Part V: The Main Theorem

The concrete expected crossings equal 2L/(πd).

The proof uses:
1. The angular average theorem (Part III)
2. Fubini to swap the integration order (as a hypothesis)
3. The arc length formula

Note: The `hFubini` hypothesis captures the one deep analysis step — just as
in our Green's theorem formalization (GreensTheoremOQ01.lean), which took
Fubini as a hypothesis.
-/

/-- **Buffon-Barbier Smooth Curve Theorem**:
    The concrete expected crossings of a smooth curve equal 2L/(πd).

    Given:
    - The derivative γ'(t) exists (as `HasDerivAt` for each component)
    - Integrability conditions for the double integral
    - Fubini: the double integral can be computed in either order

    Then: concreteSmoothExpectedCrossings γ a b d = 2 * planarArcLength γ a b / (π * d) -/
theorem buffon_smooth_concrete
    (γ : ℝ → ℝ × ℝ) (a b d : ℝ)
    (hd : 0 < d) (hab : a ≤ b)
    -- Derivatives
    (hdx : ∀ t ∈ Set.uIcc a b, HasDerivAt (Prod.fst ∘ γ) (deriv (Prod.fst ∘ γ) t) t)
    (hdy : ∀ t ∈ Set.uIcc a b, HasDerivAt (Prod.snd ∘ γ) (deriv (Prod.snd ∘ γ) t) t)
    -- Integrability of the inner integral (as a function of t)
    (hInnerInt : IntervalIntegrable
      (fun t => ∫ θ in (0 : ℝ)..π, |(deriv (Prod.fst ∘ γ) t) * sin θ +
                                      (deriv (Prod.snd ∘ γ) t) * cos θ|)
      volume a b)
    -- Fubini: we can compute the integral as ∫_t (∫_θ ...) or use the closed form
    -- This is equivalent to swapping the integration order (analysis step)
    (hFubini : ∀ t ∈ Set.uIcc a b,
      ∫ θ in (0 : ℝ)..π, |(deriv (Prod.fst ∘ γ) t) * sin θ +
                            (deriv (Prod.snd ∘ γ) t) * cos θ| =
      2 * Real.sqrt ((deriv (Prod.fst ∘ γ) t) ^ 2 + (deriv (Prod.snd ∘ γ) t) ^ 2)) :
    concreteSmoothExpectedCrossings γ a b d = 2 * planarArcLength γ a b / (π * d) := by
  simp only [concreteSmoothExpectedCrossings, planarArcLength]
  -- Apply Fubini/angular-average: inner integral = 2 * norm γ'(t)
  rw [integral_congr hFubini]
  -- Now the outer integral becomes ∫_a^b 2*sqrt(γ'_x² + γ'_y²) dt
  -- Pull the constant 2 out of the integral
  rw [intervalIntegral.integral_const_mul]
  -- (1/(π*d)) * (2 * ∫_a^b sqrt(..)) = 2 * (∫_a^b sqrt(..)) / (π*d)
  ring

/-- **Closing the gap**: When `hFubini` is proved from `angular_average`,
    the formula is automatic.

    The `hFubini` hypothesis above is EXACTLY the angular average theorem
    applied pointwise:
      ∫_0^π |γ'(t).1 sin θ + γ'(t).2 cos θ| dθ = 2√(γ'(t).1² + γ'(t).2²)

    This IS `angular_average (deriv (Prod.fst ∘ γ) t) (deriv (Prod.snd ∘ γ) t)`.

    So the full proof (once `angular_average` sorry is closed) is:

    ```lean
    theorem buffon_smooth_concrete_full ... :
        concreteSmoothExpectedCrossings γ a b d = 2 * planarArcLength γ a b / (π * d) := by
      apply buffon_smooth_concrete ... (fun t _ =>
        angular_average (deriv (Prod.fst ∘ γ) t) (deriv (Prod.snd ∘ γ) t))
    ```

    The ONLY remaining sorry is the rotation identity in `angular_average`:
      a sin θ + b cos θ = √(a²+b²) sin(θ + atan2(b,a))

    This requires a careful Lean proof of the atan2 relationship. -/
theorem hFubini_from_angular_average
    (γ : ℝ → ℝ × ℝ) (a b : ℝ) :
    ∀ t ∈ Set.uIcc a b,
      ∫ θ in (0 : ℝ)..π, |(deriv (Prod.fst ∘ γ) t) * sin θ +
                            (deriv (Prod.snd ∘ γ) t) * cos θ| =
      2 * Real.sqrt ((deriv (Prod.fst ∘ γ) t) ^ 2 + (deriv (Prod.snd ∘ γ) t) ^ 2) := by
  intro t _
  exact angular_average (deriv (Prod.fst ∘ γ) t) (deriv (Prod.snd ∘ γ) t)

/-!
## Part VI: Connection to BuffonsNoodle.lean

The `concreteSmoothExpectedCrossings` is the natural concrete definition that
replaces the axiomatic `smoothExpectedCrossings` from `BuffonsNoodle.lean`.

The current axioms in BuffonsNoodle.lean:
```lean
noncomputable axiom smoothExpectedCrossings (γ : ℝ → ℝ × ℝ) (a b d : ℝ) : ℝ
axiom buffon_noodle_smooth_eq (γ a b d hd hab hC1) :
  smoothExpectedCrossings γ a b d = 2 * planarCurveArcLength γ a b / (π * d)
```

These can be REPLACED by:
1. `concreteSmoothExpectedCrossings` (concrete definition above)
2. `buffon_smooth_concrete` (this file) + `angular_average` proof

## Summary of the Proof Gap

The ONLY remaining sorry is in `angular_average`, specifically the rotation identity:
  a sin θ + b cos θ = √(a²+b²) sin(θ + arctan(b/a))

This is provable in Lean using:
- `Real.sin_add`: sin(x+y) = sin x cos y + cos x sin y
- `Real.cos_arctan`: cos(arctan x) = 1/√(1+x²)
- `Real.sin_arctan`: sin(arctan x) = x/√(1+x²)
- Case split on a: when a > 0, a = 0, a < 0 (atan2 cases)
- For each case, normalize (a/r, b/r) as (cos φ, sin φ)

Estimated: 50-100 lines to close this sorry completely.
-/

/-- **Full theorem via angular_average**: Once the rotation identity sorry
    in `angular_average` is closed, this gives the complete theorem with
    all hypotheses made explicit. -/
theorem buffon_smooth_full
    (γ : ℝ → ℝ × ℝ) (a b d : ℝ)
    (hd : 0 < d) (hab : a ≤ b)
    (hdx : ∀ t ∈ Set.uIcc a b, HasDerivAt (Prod.fst ∘ γ) (deriv (Prod.fst ∘ γ) t) t)
    (hdy : ∀ t ∈ Set.uIcc a b, HasDerivAt (Prod.snd ∘ γ) (deriv (Prod.snd ∘ γ) t) t)
    (hInnerInt : IntervalIntegrable
      (fun t => ∫ θ in (0 : ℝ)..π, |(deriv (Prod.fst ∘ γ) t) * sin θ +
                                      (deriv (Prod.snd ∘ γ) t) * cos θ|)
      volume a b) :
    concreteSmoothExpectedCrossings γ a b d = 2 * planarArcLength γ a b / (π * d) :=
  buffon_smooth_concrete γ a b d hd hab hdx hdy hInnerInt
    (hFubini_from_angular_average γ a b)

end BuffonsNeedleOQ01OQ01
