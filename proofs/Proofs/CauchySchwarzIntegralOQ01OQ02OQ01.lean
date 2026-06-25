/-
  Discharging the Hadamard three-lines axiom
  (cauchy-schwarz-integral — OQ-01-OQ-02-OQ-01)

  The parent entry "Riesz–Thorin Interpolation from Hölder's Inequality"
  (cauchy-schwarz-integral-oq-01-oq-02) formalizes the route from Hölder's
  inequality to the Riesz–Thorin interpolation theorem. Two ingredients there
  are stated as *axioms*:

    * `hadamard_three_lines` — the Hadamard three-lines lemma (the analytic
      heart: a function bounded by `M₀` on the line `Re z = 0` and by `M₁` on
      `Re z = 1`, holomorphic in between, is bounded by `M₀^(1-t)·M₁^t` on the
      line `Re z = t`);
    * `riesz_thorin` — the interpolation theorem itself (which follows from the
      three-lines lemma).

  This file **discharges the first axiom**: it proves `hadamard_three_lines` as
  a genuine theorem, deriving it from Mathlib's complete formalization of the
  Hadamard three-lines theorem
  (`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'`).
  So the parent's open question "is the three-lines lemma available / provable in
  Lean rather than assumed?" is answered **affirmatively** — it is a theorem, not
  an axiom.

  The statement reproduced here is *identical* to the parent's axiom (same strip
  and boundary definitions, same `interpNorm θ M₀ M₁ = M₀^(1-θ)·M₁^θ`), so it can
  replace that axiom verbatim in the Riesz–Thorin development.

  Mathlib's theorem is stated for the canonical strip `re ⁻¹' [0,1]` via
  `verticalClosedStrip`/`verticalStrip`; the work here is purely the translation
  of hypotheses (continuity on the closed strip + holomorphy on the open strip
  ⇒ `DiffContOnCl`; the uniform bound ⇒ `BddAbove`; the two boundary bounds ⇒ the
  `re ⁻¹' {0}` / `re ⁻¹' {1}` bounds) and reading off `(⟨t,y⟩ : ℂ).re = t`.

  No new axioms (standard Mathlib triple inherited).

  References:
  - Mathlib: `Mathlib.Analysis.Complex.Hadamard`
    (`Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'`).
  - Stein & Shakarchi, "Complex Analysis", Ch. 4 (the three-lines lemma).

  Tags: complex-analysis, hadamard-three-lines, interpolation, riesz-thorin,
        axiom-discharge, maximum-principle
-/

import Mathlib

open Set Complex Complex.HadamardThreeLines

namespace CauchySchwarzIntegralOQ01OQ02OQ01

/-- The closed strip `{z : 0 ≤ Re z ≤ 1}` (identical to the parent entry's `closedStrip`). -/
def closedStrip : Set ℂ := {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 1}

/-- The open strip `{z : 0 < Re z < 1}` (identical to the parent entry's `openStrip`). -/
def openStrip : Set ℂ := {z : ℂ | 0 < z.re ∧ z.re < 1}

/-- The left boundary line `{z : Re z = 0}`. -/
def leftBoundary : Set ℂ := {z : ℂ | z.re = 0}

/-- The right boundary line `{z : Re z = 1}`. -/
def rightBoundary : Set ℂ := {z : ℂ | z.re = 1}

/-- The interpolated bound `M₀^(1-θ) · M₁^θ` (identical to the parent's `interpNorm`). -/
noncomputable def interpNorm (θ M₀ M₁ : ℝ) : ℝ := M₀ ^ (1 - θ) * M₁ ^ θ

/-- **The Hadamard three-lines lemma — now a theorem, not an axiom.**

If `F` is continuous on the closed strip `0 ≤ Re z ≤ 1`, holomorphic on the open
strip, uniformly bounded there, and satisfies `‖F‖ ≤ M₀` on the line `Re z = 0`
and `‖F‖ ≤ M₁` on `Re z = 1`, then on the line `Re z = t` (for `0 ≤ t ≤ 1`)
`‖F (t + i y)‖ ≤ M₀^(1-t) · M₁^t`.

This reproduces the parent entry's `hadamard_three_lines` axiom *verbatim* and
proves it from Mathlib's `norm_le_interp_of_mem_verticalClosedStrip₀₁'`. -/
theorem hadamard_three_lines
    (F : ℂ → ℂ) (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hcont : ContinuousOn F closedStrip)
    (hdiff : ∀ z ∈ openStrip, DifferentiableAt ℂ F z)
    (hbound : ∀ z ∈ closedStrip, ‖F z‖ ≤ max M₀ M₁)
    (hleft : ∀ z ∈ leftBoundary, ‖F z‖ ≤ M₀)
    (hright : ∀ z ∈ rightBoundary, ‖F z‖ ≤ M₁)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (y : ℝ) :
    ‖F (⟨t, y⟩ : ℂ)‖ ≤ interpNorm t M₀ M₁ := by
  -- bridge the local strip definitions to Mathlib's `verticalStrip`/`verticalClosedStrip`
  have hcs : closedStrip = verticalClosedStrip 0 1 := by
    ext z; simp [closedStrip, verticalClosedStrip, mem_preimage, mem_Icc]
  have hos : openStrip = verticalStrip 0 1 := by
    ext z; simp [openStrip, verticalStrip, mem_preimage, mem_Ioo]
  -- `(⟨t, y⟩ : ℂ)` lies in the closed strip
  have hzmem : (⟨t, y⟩ : ℂ) ∈ verticalClosedStrip 0 1 := by
    simp only [verticalClosedStrip, mem_preimage, mem_Icc]
    exact ⟨ht₀, ht₁⟩
  -- `closure (verticalStrip 0 1) = verticalClosedStrip 0 1`
  have hclosure : closure (verticalStrip 0 1) = verticalClosedStrip 0 1 := by
    rw [verticalStrip, verticalClosedStrip, closure_preimage_re, closure_Ioo (zero_ne_one)]
  -- holomorphy on the open strip + continuity on the closed strip ⇒ `DiffContOnCl`
  have hd : DiffContOnCl ℂ F (verticalStrip 0 1) := by
    refine ⟨?_, ?_⟩
    · intro z hz
      rw [← hos] at hz
      exact (hdiff z hz).differentiableWithinAt
    · rw [hclosure, ← hcs]; exact hcont
  -- the uniform bound gives `BddAbove`
  have hB : BddAbove ((norm ∘ F) '' verticalClosedStrip 0 1) := by
    refine ⟨max M₀ M₁, ?_⟩
    rintro w ⟨z, hz, rfl⟩
    rw [← hcs] at hz
    exact hbound z hz
  -- the two boundary bounds in Mathlib's `re ⁻¹' {·}` form
  have ha : ∀ z ∈ re ⁻¹' {(0 : ℝ)}, ‖F z‖ ≤ M₀ := by
    intro z hz
    exact hleft z (by simpa [leftBoundary] using hz)
  have hb : ∀ z ∈ re ⁻¹' {(1 : ℝ)}, ‖F z‖ ≤ M₁ := by
    intro z hz
    exact hright z (by simpa [rightBoundary] using hz)
  -- apply Mathlib's three-lines theorem and read off `(⟨t,y⟩).re = t`
  have key := norm_le_interp_of_mem_verticalClosedStrip₀₁' F hzmem hd hB ha hb
  simpa [interpNorm] using key

/-- **Corollary (logarithmic / convexity form).** Under the same hypotheses, when
`F (t + iy) ≠ 0` the logarithm of `‖F‖` is convex along the strip:
`log ‖F (t+iy)‖ ≤ (1-t)·log M₀ + t·log M₁`. This is the form used to interpolate
operator norms in the Riesz–Thorin theorem. -/
theorem hadamard_three_lines_log
    (F : ℂ → ℂ) (M₀ M₁ : ℝ) (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hcont : ContinuousOn F closedStrip)
    (hdiff : ∀ z ∈ openStrip, DifferentiableAt ℂ F z)
    (hbound : ∀ z ∈ closedStrip, ‖F z‖ ≤ max M₀ M₁)
    (hleft : ∀ z ∈ leftBoundary, ‖F z‖ ≤ M₀)
    (hright : ∀ z ∈ rightBoundary, ‖F z‖ ≤ M₁)
    (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (y : ℝ)
    (hFpos : 0 < ‖F (⟨t, y⟩ : ℂ)‖) :
    Real.log ‖F (⟨t, y⟩ : ℂ)‖ ≤ (1 - t) * Real.log M₀ + t * Real.log M₁ := by
  have htl := hadamard_three_lines F M₀ M₁ hM₀ hM₁ hcont hdiff hbound hleft hright t ht₀ ht₁ y
  have hlog : Real.log (interpNorm t M₀ M₁) = (1 - t) * Real.log M₀ + t * Real.log M₁ := by
    rw [interpNorm, Real.log_mul (by positivity) (by positivity),
      Real.log_rpow hM₀, Real.log_rpow hM₁]
  calc Real.log ‖F (⟨t, y⟩ : ℂ)‖
      ≤ Real.log (interpNorm t M₀ M₁) := Real.log_le_log hFpos htl
    _ = (1 - t) * Real.log M₀ + t * Real.log M₁ := hlog

end CauchySchwarzIntegralOQ01OQ02OQ01
