/-
  Integrating Buffon's Noodle via Concrete Expected Crossings
  Open Question: buffons-needle-oq-01-oq-01-oq-01

  This file demonstrates that the two axioms in BuffonsNoodle.lean:
    noncomputable axiom smoothExpectedCrossings (γ : ℝ → ℝ × ℝ) (a b d : ℝ) : ℝ
    axiom buffon_noodle_smooth_eq (γ a b d hd hab hC1) : ...

  can be replaced entirely by the concrete definition `concreteSmoothExpectedCrossings`
  from BuffonsNeedleOQ01OQ01.lean, with all key theorems provable without axioms.

  Main Results:
  - `concreteSmoothExpectedCrossings_nonneg`: expected crossings ≥ 0 (direct, no derivative hyps)
  - `concrete_main_theorem`: the Buffon-Barbier formula (axiom-free version)
  - `concrete_shape_independence`: same arc length → same expected crossings
  - `concrete_crossings_nonneg_via_formula`: nonnegativity via the formula + arc-length bound

  Key insight: `buffon_smooth_full` in BuffonsNeedleOQ01OQ01 replaces `buffon_noodle_smooth_eq`
  with an axiom-free proof under explicit (non-axiomatic) hypotheses.

  Axioms: 0
  Sorries: 0
-/

import Proofs.BuffonsNeedleOQ01OQ01

namespace BuffonsNeedleOQ01OQ01OQ01

open Real intervalIntegral MeasureTheory BuffonsNeedleOQ01OQ01

-- ============================================================
-- Section I: Nonnegativity (no curve hypotheses)
-- ============================================================

/-- **Nonnegativity of concrete expected crossings**: For any curve γ and line spacing d > 0,
    the concrete expected crossings are nonneg when a ≤ b.

    Proof: The integrand |·| ≥ 0 everywhere; scaling by 1/(π·d) > 0 preserves this. -/
theorem concreteSmoothExpectedCrossings_nonneg
    (γ : ℝ → ℝ × ℝ) (a b d : ℝ) (hab : a ≤ b) (hd : 0 < d) :
    0 ≤ concreteSmoothExpectedCrossings γ a b d := by
  simp only [concreteSmoothExpectedCrossings]
  apply mul_nonneg
  · exact div_nonneg (by norm_num) (mul_pos pi_pos hd).le
  · apply integral_nonneg hab
    intro t _
    apply integral_nonneg pi_pos.le
    intro θ _
    exact abs_nonneg _

-- ============================================================
-- Section II: The Main Theorem (axiom-free Buffon-Barbier)
-- ============================================================

/-- **Concrete Buffon-Barbier Theorem**: The axiom-free version of `buffon_noodle_smooth_eq`.

    For a C¹ curve γ : ℝ → ℝ × ℝ on [a,b] with parallel line grid spacing d > 0,
    the concrete expected number of crossings equals 2·arcLength/(π·d).

    Unlike `buffon_noodle_smooth_eq` in BuffonsNoodle.lean (which was an axiom),
    this is a genuine theorem — a direct consequence of `angular_average` + Fubini. -/
theorem concrete_main_theorem
    (γ : ℝ → ℝ × ℝ) (a b d : ℝ)
    (hd : 0 < d) (hab : a ≤ b)
    (hdx : ∀ t ∈ Set.uIcc a b, HasDerivAt (Prod.fst ∘ γ) (deriv (Prod.fst ∘ γ) t) t)
    (hdy : ∀ t ∈ Set.uIcc a b, HasDerivAt (Prod.snd ∘ γ) (deriv (Prod.snd ∘ γ) t) t)
    (hInnerInt : IntervalIntegrable
      (fun t => ∫ θ in (0 : ℝ)..π, |(deriv (Prod.fst ∘ γ) t) * sin θ +
                                      (deriv (Prod.snd ∘ γ) t) * cos θ|)
      volume a b) :
    concreteSmoothExpectedCrossings γ a b d = 2 * planarArcLength γ a b / (π * d) :=
  buffon_smooth_full γ a b d hd hab hdx hdy hInnerInt

-- ============================================================
-- Section III: Shape Independence (no axioms)
-- ============================================================

/-- **Shape Independence**: Two smooth curves with the same arc length have the same
    concrete expected number of crossings.

    This is the axiom-free replacement for `smooth_shape_independence` in BuffonsNoodle.lean,
    which relied on `buffon_noodle_smooth_eq` (an axiom). -/
theorem concrete_shape_independence
    (γ₁ γ₂ : ℝ → ℝ × ℝ) (a₁ b₁ a₂ b₂ d : ℝ)
    (hd : 0 < d)
    (h1 : a₁ ≤ b₁) (h2 : a₂ ≤ b₂)
    (hdx₁ : ∀ t ∈ Set.uIcc a₁ b₁, HasDerivAt (Prod.fst ∘ γ₁) (deriv (Prod.fst ∘ γ₁) t) t)
    (hdy₁ : ∀ t ∈ Set.uIcc a₁ b₁, HasDerivAt (Prod.snd ∘ γ₁) (deriv (Prod.snd ∘ γ₁) t) t)
    (hInt₁ : IntervalIntegrable
      (fun t => ∫ θ in (0:ℝ)..π, |(deriv (Prod.fst ∘ γ₁) t) * sin θ +
                                    (deriv (Prod.snd ∘ γ₁) t) * cos θ|)
      volume a₁ b₁)
    (hdx₂ : ∀ t ∈ Set.uIcc a₂ b₂, HasDerivAt (Prod.fst ∘ γ₂) (deriv (Prod.fst ∘ γ₂) t) t)
    (hdy₂ : ∀ t ∈ Set.uIcc a₂ b₂, HasDerivAt (Prod.snd ∘ γ₂) (deriv (Prod.snd ∘ γ₂) t) t)
    (hInt₂ : IntervalIntegrable
      (fun t => ∫ θ in (0:ℝ)..π, |(deriv (Prod.fst ∘ γ₂) t) * sin θ +
                                    (deriv (Prod.snd ∘ γ₂) t) * cos θ|)
      volume a₂ b₂)
    (hLen : planarArcLength γ₁ a₁ b₁ = planarArcLength γ₂ a₂ b₂) :
    concreteSmoothExpectedCrossings γ₁ a₁ b₁ d =
    concreteSmoothExpectedCrossings γ₂ a₂ b₂ d := by
  rw [concrete_main_theorem γ₁ a₁ b₁ d hd h1 hdx₁ hdy₁ hInt₁,
      concrete_main_theorem γ₂ a₂ b₂ d hd h2 hdx₂ hdy₂ hInt₂, hLen]

-- ============================================================
-- Section IV: Nonnegativity via Formula
-- ============================================================

/-- **Nonnegativity via formula**: Under derivative hypotheses, the concrete expected
    crossings are nonneg because arc length is nonneg and 2/(π·d) > 0. -/
theorem concrete_crossings_nonneg_via_formula
    (γ : ℝ → ℝ × ℝ) (a b d : ℝ)
    (hd : 0 < d) (hab : a ≤ b)
    (hdx : ∀ t ∈ Set.uIcc a b, HasDerivAt (Prod.fst ∘ γ) (deriv (Prod.fst ∘ γ) t) t)
    (hdy : ∀ t ∈ Set.uIcc a b, HasDerivAt (Prod.snd ∘ γ) (deriv (Prod.snd ∘ γ) t) t)
    (hInnerInt : IntervalIntegrable
      (fun t => ∫ θ in (0:ℝ)..π, |(deriv (Prod.fst ∘ γ) t) * sin θ +
                                    (deriv (Prod.snd ∘ γ) t) * cos θ|)
      volume a b) :
    0 ≤ concreteSmoothExpectedCrossings γ a b d := by
  rw [concrete_main_theorem γ a b d hd hab hdx hdy hInnerInt]
  apply div_nonneg
  · apply mul_nonneg (by norm_num)
    simp only [planarArcLength]
    apply integral_nonneg hab
    intro t _
    exact Real.sqrt_nonneg _
  · exact (mul_pos pi_pos hd).le

end BuffonsNeedleOQ01OQ01OQ01
