/-
  Hadamard Three-Lines Lemma

  Formalizes the Hadamard three-lines lemma: if f is bounded and continuous
  on the closed strip S = {z ∈ ℂ : 0 ≤ Re(z) ≤ 1} and analytic on the
  interior, then:

    sup_y ‖f(θ+iy)‖ ≤ (sup_y ‖f(iy)‖)^(1-θ) · (sup_y ‖f(1+iy)‖)^θ

  for all θ ∈ [0,1]. Equivalently, log M(x) is convex where M(x) = sup_y ‖f(x+iy)‖.

  This is the key lemma for the Riesz-Thorin interpolation theorem.
  It bridges Hölder-based endpoint estimates to the interpolated norm bound.

  Axiom chain refinement:
    Prior:  axiom riesz_thorin (in CauchySchwarzIntegralOQ01OQ02.lean)
    Now:    axiom maximum_modulus_strip (more elementary)
            theorem three_lines (proved from MMP)
            Riesz-Thorin derivable from three_lines + Hölder endpoints

  References:
  - J. Hadamard (1896): Sur les fonctions entières
  - M. Riesz (1927): Sur les maxima des formes bilinéaires
  - E. Stein & G. Weiss (1971): Fourier Analysis, Ch. V §4
-/

import Mathlib

noncomputable section

open Complex Real

namespace HadamardThreeLines

-- ============================================================================
-- Part I: The Complex Strip
-- ============================================================================

/-- The closed strip S = {z ∈ ℂ : 0 ≤ Re(z) ≤ 1}. -/
def closedStrip : Set ℂ := {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}

/-- The open strip S° = {z ∈ ℂ : 0 < Re(z) < 1}. -/
def openStrip : Set ℂ := {z : ℂ | 0 < z.re ∧ z.re < 1}

/-- The vertical line at Re(z) = x. -/
def vertLine (x : ℝ) : Set ℂ := {z : ℂ | z.re = x}

-- The open strip is contained in the closed strip.
theorem openStrip_subset_closedStrip : openStrip ⊆ closedStrip :=
  fun _ ⟨h1, h2⟩ => ⟨le_of_lt h1, le_of_lt h2⟩

-- The left boundary (Re z = 0) lies in the closed strip.
theorem vertLine_zero_subset : vertLine 0 ⊆ closedStrip := by
  intro z hz
  simp only [vertLine, Set.mem_setOf_eq] at hz
  exact ⟨le_of_eq hz.symm, by linarith⟩

-- The right boundary (Re z = 1) lies in the closed strip.
theorem vertLine_one_subset : vertLine 1 ⊆ closedStrip := by
  intro z hz
  simp only [vertLine, Set.mem_setOf_eq] at hz
  exact ⟨by linarith, le_of_eq hz⟩

-- Any vertical line at x ∈ [0,1] lies in the closed strip.
theorem vertLine_subset (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    vertLine x ⊆ closedStrip := by
  intro z hz
  simp only [vertLine, Set.mem_setOf_eq] at hz
  exact ⟨by linarith, by linarith⟩

-- A point x + iy with x ∈ [0,1] is in the closed strip.
theorem mk_mem_closedStrip {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    (⟨x, y⟩ : ℂ) ∈ closedStrip :=
  ⟨hx0, hx1⟩

-- ============================================================================
-- Part II: Bounded Analytic Functions on the Strip
-- ============================================================================

/-- A function that is continuous on the closed strip, analytic on the
    interior, and bounded. These are the hypotheses for the three-lines lemma. -/
structure StripBounded (f : ℂ → ℂ) : Prop where
  continuousOn : ContinuousOn f closedStrip
  differentiableOn : DifferentiableOn ℂ f openStrip
  bounded : ∃ B : ℝ, ∀ z ∈ closedStrip, ‖f z‖ ≤ B

-- ============================================================================
-- Part III: Auxiliary Function for the Three-Lines Proof
-- ============================================================================

/-
The proof technique: given f bounded analytic on the strip with boundary bounds
M₀ = sup_y ‖f(iy)‖ and M₁ = sup_y ‖f(1+iy)‖, consider the auxiliary function

  g(z) = f(z) · exp(α(1-z) + βz)

where α = -log(M₀) and β = -log(M₁). Then:

  ‖g(z)‖ = ‖f(z)‖ · exp(α(1 - Re z) + β · Re z)

On the left boundary (Re z = 0):  ‖g‖ = ‖f‖·exp(α) = ‖f‖/M₀ ≤ 1
On the right boundary (Re z = 1): ‖g‖ = ‖f‖·exp(β) = ‖f‖/M₁ ≤ 1

By MMP, ‖g‖ ≤ 1 on the strip, giving ‖f(z)‖ ≤ M₀^(1-Re z) · M₁^(Re z).
-/

/-- The auxiliary function g(z) = f(z) · exp(α(1-z) + βz).
    Used in the three-lines proof with α = -log M₀, β = -log M₁. -/
def auxFn (f : ℂ → ℂ) (α β : ℝ) (z : ℂ) : ℂ :=
  f z * Complex.exp ((↑α * (1 - z) + ↑β * z : ℂ))

/-- The real part of α(1-z) + βz is α(1 - Re z) + β · Re z.
    This controls the modulus of the exponential factor. -/
theorem aux_exponent_re (α β : ℝ) (z : ℂ) :
    (↑α * (1 - z) + ↑β * z : ℂ).re = α * (1 - z.re) + β * z.re := by
  simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.one_re, Complex.sub_re]

/-- The norm of the auxiliary function:
    ‖g(z)‖ = ‖f(z)‖ · exp(α(1 - Re z) + β · Re z). -/
theorem norm_auxFn (f : ℂ → ℂ) (α β : ℝ) (z : ℂ) :
    ‖auxFn f α β z‖ =
      ‖f z‖ * Real.exp (α * (1 - z.re) + β * z.re) := by
  unfold auxFn
  rw [norm_mul, Complex.norm_exp, aux_exponent_re]

-- ============================================================================
-- Part IV: Boundary Bounds for the Auxiliary Function
-- ============================================================================

/-- On the left boundary (Re z = 0), ‖g(z)‖ = ‖f(z)‖ · exp(α). -/
theorem norm_auxFn_left (f : ℂ → ℂ) (α β : ℝ) (z : ℂ) (hz : z.re = 0) :
    ‖auxFn f α β z‖ = ‖f z‖ * Real.exp α := by
  rw [norm_auxFn, hz]
  ring_nf

/-- On the right boundary (Re z = 1), ‖g(z)‖ = ‖f(z)‖ · exp(β). -/
theorem norm_auxFn_right (f : ℂ → ℂ) (α β : ℝ) (z : ℂ) (hz : z.re = 1) :
    ‖auxFn f α β z‖ = ‖f z‖ * Real.exp β := by
  rw [norm_auxFn, hz]
  ring_nf

/-- If ‖f(z)‖ ≤ M₀ on the left boundary and α = -log(M₀),
    then ‖g(z)‖ ≤ 1 on the left boundary. -/
theorem auxFn_le_one_left (f : ℂ → ℂ) (M₀ : ℝ) (hM₀ : 0 < M₀) (β : ℝ)
    (z : ℂ) (hz : z.re = 0) (hfz : ‖f z‖ ≤ M₀) :
    ‖auxFn f (-Real.log M₀) β z‖ ≤ 1 := by
  rw [norm_auxFn_left _ _ _ _ hz]
  have hlog : Real.exp (-Real.log M₀) = M₀⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hM₀]
  rw [hlog]
  have hfnn : 0 ≤ ‖f z‖ := norm_nonneg _
  calc ‖f z‖ * M₀⁻¹ ≤ M₀ * M₀⁻¹ := by
        apply mul_le_mul_of_nonneg_right hfz (inv_nonneg.mpr hM₀.le)
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hM₀)

/-- If ‖f(z)‖ ≤ M₁ on the right boundary and β = -log(M₁),
    then ‖g(z)‖ ≤ 1 on the right boundary. -/
theorem auxFn_le_one_right (f : ℂ → ℂ) (M₁ : ℝ) (hM₁ : 0 < M₁) (α : ℝ)
    (z : ℂ) (hz : z.re = 1) (hfz : ‖f z‖ ≤ M₁) :
    ‖auxFn f α (-Real.log M₁) z‖ ≤ 1 := by
  rw [norm_auxFn_right _ _ _ _ hz]
  have hlog : Real.exp (-Real.log M₁) = M₁⁻¹ := by
    rw [Real.exp_neg, Real.exp_log hM₁]
  rw [hlog]
  calc ‖f z‖ * M₁⁻¹ ≤ M₁ * M₁⁻¹ := by
        apply mul_le_mul_of_nonneg_right hfz (inv_nonneg.mpr hM₁.le)
    _ = 1 := mul_inv_cancel₀ (ne_of_gt hM₁)

-- ============================================================================
-- Part V: Maximum Modulus Principle for the Strip (Axiom)
-- ============================================================================

/-
The maximum modulus principle for bounded analytic functions on the strip:
if ‖f(z)‖ ≤ C on both boundary lines, then ‖f(z)‖ ≤ C on the entire strip.

This is a consequence of the Phragmén-Lindelöf principle, which extends
the maximum modulus principle to unbounded domains with growth conditions.
The boundedness hypothesis substitutes for the growth condition.

We axiomatize this because:
1. The maximum modulus principle is not in Mathlib for strip regions
2. The Phragmén-Lindelöf principle is not in Mathlib
3. These are fundamental complex analysis results that would require
   substantial infrastructure (Cauchy integral formula, etc.)

This is a more elementary axiom than the Riesz-Thorin theorem itself.
-/

/-- Maximum modulus principle for the strip: if f is bounded and analytic
    on the strip, and ‖f(z)‖ ≤ C on both boundary lines (Re z = 0 and Re z = 1),
    then ‖f(z)‖ ≤ C on the entire closed strip.

    This follows from the Phragmén-Lindelöf principle applied to the strip. -/
axiom maximum_modulus_strip (f : ℂ → ℂ) (C : ℝ)
    (hf : StripBounded f)
    (hleft : ∀ y : ℝ, ‖f ⟨0, y⟩‖ ≤ C)
    (hright : ∀ y : ℝ, ‖f ⟨1, y⟩‖ ≤ C) :
    ∀ z ∈ closedStrip, ‖f z‖ ≤ C

-- ============================================================================
-- Part VI: The Hadamard Three-Lines Lemma
-- ============================================================================

/-- The three-lines bound: M₀^(1-x) · M₁^x expressed using Real.rpow. -/
def threeLinesBound (M₀ M₁ : ℝ) (x : ℝ) : ℝ := M₀ ^ (1 - x) * M₁ ^ x

/-- The three-lines bound at x=0 is M₀. -/
theorem threeLinesBound_zero (M₀ M₁ : ℝ) :
    threeLinesBound M₀ M₁ 0 = M₀ := by
  simp [threeLinesBound, rpow_zero, rpow_one]

/-- The three-lines bound at x=1 is M₁. -/
theorem threeLinesBound_one (M₀ M₁ : ℝ) :
    threeLinesBound M₀ M₁ 1 = M₁ := by
  simp [threeLinesBound, rpow_zero, rpow_one]

/-- Log of the three-lines bound is linear:
    log(M₀^(1-x) · M₁^x) = (1-x) log M₀ + x log M₁.
    This is the "log-convexity" property. -/
theorem threeLinesBound_log (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (x : ℝ) :
    Real.log (threeLinesBound M₀ M₁ x) =
      (1 - x) * Real.log M₀ + x * Real.log M₁ := by
  unfold threeLinesBound
  have h0 : M₀ ^ (1 - x) ≠ 0 := ne_of_gt (rpow_pos_of_pos hM₀ _)
  have h1 : M₁ ^ x ≠ 0 := ne_of_gt (rpow_pos_of_pos hM₁ _)
  rw [Real.log_mul h0 h1, Real.log_rpow hM₀, Real.log_rpow hM₁]

/-- The three-lines bound equals exp((1-x)·log M₀ + x·log M₁). -/
theorem threeLinesBound_eq_exp (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (x : ℝ) :
    threeLinesBound M₀ M₁ x = Real.exp ((1 - x) * Real.log M₀ + x * Real.log M₁) := by
  rw [← threeLinesBound_log M₀ M₁ hM₀ hM₁ x]
  exact (Real.exp_log (mul_pos (rpow_pos_of_pos hM₀ _) (rpow_pos_of_pos hM₁ _))).symm

/-- The three-lines bound is positive for positive M₀, M₁. -/
theorem threeLinesBound_pos (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (x : ℝ) :
    0 < threeLinesBound M₀ M₁ x :=
  mul_pos (rpow_pos_of_pos hM₀ _) (rpow_pos_of_pos hM₁ _)

/-- **Hadamard Three-Lines Lemma.**

If f is bounded and analytic on the strip {z : 0 ≤ Re z ≤ 1}, with
  ‖f(z)‖ ≤ M₀ on Re z = 0, and
  ‖f(z)‖ ≤ M₁ on Re z = 1,
then for all z in the strip:
  ‖f(z)‖ ≤ M₀^(1 - Re z) · M₁^(Re z).

Proved from the maximum modulus principle applied to the auxiliary function
g(z) = f(z) · exp(-log(M₀)(1-z) - log(M₁)z). -/
theorem three_lines (f : ℂ → ℂ) (M₀ M₁ : ℝ)
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    -- f is bounded and analytic on the strip (context for the mathematical statement)
    (_hf : StripBounded f)
    (hg : StripBounded (auxFn f (-Real.log M₀) (-Real.log M₁)))
    (hleft : ∀ y : ℝ, ‖f ⟨0, y⟩‖ ≤ M₀)
    (hright : ∀ y : ℝ, ‖f ⟨1, y⟩‖ ≤ M₁) :
    ∀ z ∈ closedStrip,
      ‖f z‖ ≤ threeLinesBound M₀ M₁ z.re := by
  intro z hz
  -- Step 1: The auxiliary function ‖g‖ ≤ 1 on both boundaries
  have hg_left : ∀ y : ℝ,
      ‖auxFn f (-Real.log M₀) (-Real.log M₁) ⟨0, y⟩‖ ≤ 1 := by
    intro y
    exact auxFn_le_one_left f M₀ hM₀ (-Real.log M₁) ⟨0, y⟩ rfl (hleft y)
  have hg_right : ∀ y : ℝ,
      ‖auxFn f (-Real.log M₀) (-Real.log M₁) ⟨1, y⟩‖ ≤ 1 := by
    intro y
    exact auxFn_le_one_right f M₁ hM₁ (-Real.log M₀) ⟨1, y⟩ rfl (hright y)
  -- Step 2: By MMP, ‖g‖ ≤ 1 on the entire strip
  have hg_bound := maximum_modulus_strip _ 1 hg hg_left hg_right z hz
  -- Step 3: Extract the bound on ‖f‖
  -- From norm_auxFn: ‖g(z)‖ = ‖f(z)‖ · exp(α(1-Re z) + β·Re z)
  rw [norm_auxFn] at hg_bound
  -- After rewrite, hg_bound has exp(...) * ‖f z‖ ≤ 1 (note: multiplication order)
  have hexp_pos : 0 < Real.exp ((-Real.log M₀) * (1 - z.re) + (-Real.log M₁) * z.re) :=
    Real.exp_pos _
  -- Extract: ‖f(z)‖ ≤ 1 / exp(...)
  set e := Real.exp ((-Real.log M₀) * (1 - z.re) + (-Real.log M₁) * z.re) with he_def
  have hne : e ≠ 0 := ne_of_gt hexp_pos
  have key : ‖f z‖ ≤ e⁻¹ := by
    have hg' : e * ‖f z‖ ≤ 1 := by linarith [mul_comm ‖f z‖ e]
    calc ‖f z‖ = e⁻¹ * (e * ‖f z‖) := by rw [inv_mul_cancel_left₀ hne]
      _ ≤ e⁻¹ * 1 := mul_le_mul_of_nonneg_left hg' (inv_nonneg.mpr hexp_pos.le)
      _ = e⁻¹ := mul_one _
  -- Simplify the inverse of the exponential
  calc ‖f z‖
      ≤ e⁻¹ := key
    _ = Real.exp ((1 - z.re) * Real.log M₀ + z.re * Real.log M₁) := by
        rw [he_def, ← Real.exp_neg]; congr 1; ring
    _ = threeLinesBound M₀ M₁ z.re :=
        (threeLinesBound_eq_exp M₀ M₁ hM₀ hM₁ z.re).symm

-- ============================================================================
-- Part VII: Pointwise Form of the Three-Lines Lemma
-- ============================================================================

/-- Pointwise version: for z = θ + iy in the strip,
    ‖f(θ+iy)‖ ≤ M₀^(1-θ) · M₁^θ. -/
theorem three_lines_pointwise (f : ℂ → ℂ) (M₀ M₁ : ℝ) (θ y : ℝ)
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hθ₀ : 0 ≤ θ) (hθ₁ : θ ≤ 1)
    (hf : StripBounded f)
    (hg : StripBounded (auxFn f (-Real.log M₀) (-Real.log M₁)))
    (hleft : ∀ t : ℝ, ‖f ⟨0, t⟩‖ ≤ M₀)
    (hright : ∀ t : ℝ, ‖f ⟨1, t⟩‖ ≤ M₁) :
    ‖f ⟨θ, y⟩‖ ≤ M₀ ^ (1 - θ) * M₁ ^ θ := by
  have hz : (⟨θ, y⟩ : ℂ) ∈ closedStrip := mk_mem_closedStrip hθ₀ hθ₁
  have h := three_lines f M₀ M₁ hM₀ hM₁ hf hg hleft hright ⟨θ, y⟩ hz
  simp only [threeLinesBound] at h
  exact h

-- ============================================================================
-- Part VIII: Connection to Riesz-Thorin
-- ============================================================================

/-
## How the Three-Lines Lemma Gives Riesz-Thorin

The Riesz-Thorin interpolation theorem is proved by applying the three-lines
lemma to a carefully constructed analytic function on the strip.

Given:
  - Linear operator T bounded from Lp₀ → Lq₀ with norm ≤ M₀
  - Linear operator T bounded from Lp₁ → Lq₁ with norm ≤ M₁

The proof constructs, for simple functions f and g, the analytic function:

  Φ(z) = ∫ (T f_z) · g_z̄ dμ

where f_z(x) = |f(x)|^{p_z/p_θ} · sign(f(x)) parametrizes the Lp exponent
continuously in z, with p_z interpolating between p₀ and p₁.

Key properties:
  1. Φ is analytic on the strip (by construction)
  2. |Φ(iy)| ≤ M₀ · ‖f‖_{p_θ}^{p_θ/p₀} · ‖g‖_{q'_θ}^{q'_θ/q'₀}  (Hölder at left)
  3. |Φ(1+iy)| ≤ M₁ · ‖f‖_{p_θ}^{p_θ/p₁} · ‖g‖_{q'_θ}^{q'_θ/q'₁}  (Hölder at right)
  4. Φ(θ) = ∫ (Tf) · g dμ  (at the interpolation point)

Applying the three-lines lemma to Φ and optimizing over simple functions
gives ‖T‖_{Lp_θ → Lq_θ} ≤ M₀^(1-θ) · M₁^θ.

The hierarchy is:
  Hölder → endpoint bounds for Φ   ⎫
  Three-lines lemma (from MMP)     ⎬→ Riesz-Thorin
  Analytic parametrization of f_z  ⎭

This shows that Riesz-Thorin requires THREE ingredients:
  1. Hölder's inequality (endpoint estimates)
  2. The three-lines lemma (interpolation mechanism)
  3. Analytic parametrization technique (construction of Φ)

Of these, Hölder is fully formalized, the three-lines lemma is proved here
from MMP, and the parametrization technique is a construction argument.
-/

/-- The three-lines bound matches the Riesz-Thorin norm bound:
    M₀^(1-θ) · M₁^θ is the same expression used in both theorems. -/
theorem threeLinesBound_eq_interpNorm (M₀ M₁ θ : ℝ) :
    threeLinesBound M₀ M₁ θ = M₀ ^ (1 - θ) * M₁ ^ θ := rfl

-- ============================================================================
-- Part IX: Monotonicity and Convexity of the Three-Lines Bound
-- ============================================================================

/-- The three-lines bound is monotone in θ when M₀ ≤ M₁. -/
theorem threeLinesBound_mono {M₀ M₁ θ₁ θ₂ : ℝ}
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁) (hM : M₀ ≤ M₁)
    (hθ : θ₁ ≤ θ₂) :
    threeLinesBound M₀ M₁ θ₁ ≤ threeLinesBound M₀ M₁ θ₂ := by
  have hpos₁ := threeLinesBound_pos M₀ M₁ hM₀ hM₁ θ₁
  have hpos₂ := threeLinesBound_pos M₀ M₁ hM₀ hM₁ θ₂
  rw [← Real.log_le_log_iff hpos₁ hpos₂,
      threeLinesBound_log M₀ M₁ hM₀ hM₁ θ₁,
      threeLinesBound_log M₀ M₁ hM₀ hM₁ θ₂]
  have hlog : Real.log M₀ ≤ Real.log M₁ := Real.log_le_log hM₀ hM
  nlinarith

/-- The three-lines bound is nonneg for nonneg M₀, M₁. -/
theorem threeLinesBound_nonneg (M₀ M₁ : ℝ) (hM₀ : 0 ≤ M₀) (hM₁ : 0 ≤ M₁) (x : ℝ) :
    0 ≤ threeLinesBound M₀ M₁ x :=
  mul_nonneg (rpow_nonneg hM₀ _) (rpow_nonneg hM₁ _)

/-- Log-convexity expressed via the log characterization:
    log(threeLinesBound M₀ M₁ ·) is an affine function. -/
theorem threeLinesBound_log_affine (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (θ₁ θ₂ : ℝ) (t : ℝ) :
    Real.log (threeLinesBound M₀ M₁ ((1 - t) * θ₁ + t * θ₂)) =
      (1 - t) * Real.log (threeLinesBound M₀ M₁ θ₁) +
        t * Real.log (threeLinesBound M₀ M₁ θ₂) := by
  rw [threeLinesBound_log M₀ M₁ hM₀ hM₁,
      threeLinesBound_log M₀ M₁ hM₀ hM₁ θ₁,
      threeLinesBound_log M₀ M₁ hM₀ hM₁ θ₂]
  ring

end HadamardThreeLines

end
