/-
  Aristotle targets for FundamentalTheoremCalculusStokes
  Routine supporting lemmas for automated proof search.
  See FundamentalTheoremCalculusStokes.lean for the main formalization.

  Criteria for inclusion:
  - d² = 0 (Clairaut's theorem) — well-known calculus result
  - Green's theorem for rectangles — well-known result, full proof exists in GreensTheoremOQ01.lean
  - Clean theorem statements with no definition sorries
  - No axioms, no open conjectures

  Session 2026-05-06: Proved dd_eq_zero_2D using:
  - HasFDerivAt.comp_hasDerivAt to connect deriv to fderiv evaluations
  - HasDerivAt.clm_apply to differentiate fderiv evaluations
  - ContDiffAt.isSymmSndFDerivAt for the symmetry of the second Fréchet derivative
-/
import Mathlib

namespace GeneralizedStokes

open MeasureTheory Set Filter Topology intervalIntegral

/-- A 1-form in 2D: ω = P(x,y)dx + Q(x,y)dy. -/
structure OneForm2D where
  P : ℝ × ℝ → ℝ
  Q : ℝ × ℝ → ℝ

/-- d₀(f) = (∂f/∂x)dx + (∂f/∂y)dy. -/
noncomputable def extDeriv0_2D (f : ℝ × ℝ → ℝ) : OneForm2D where
  P := fun p => deriv (fun x => f (x, p.2)) p.1
  Q := fun p => deriv (fun y => f (p.1, y)) p.2

/-- d₁(Pdx + Qdy) = (∂Q/∂x - ∂P/∂y) dx∧dy. -/
noncomputable def extDeriv1_2D (ω : OneForm2D) : ℝ × ℝ → ℝ :=
  fun p => deriv (fun x => ω.Q (x, p.2)) p.1 -
            deriv (fun y => ω.P (p.1, y)) p.2

noncomputable def lineIntegralRect (ω : OneForm2D) (a b c d : ℝ) : ℝ :=
  (∫ x in a..b, ω.P (x, c)) + (∫ y in c..d, ω.Q (b, y)) -
  (∫ x in a..b, ω.P (x, d)) - (∫ y in c..d, ω.Q (a, y))

noncomputable def areaIntegralRect (h : ℝ × ℝ → ℝ) (a b c d : ℝ) : ℝ :=
  ∫ y in c..d, ∫ x in a..b, h (x, y)

/-- d² = 0 (Clairaut's theorem): mixed partials commute for C² functions.

    The key steps of the proof:
    1. Express ∂f/∂y(x, p.2) as fderiv ℝ f (x, p.2) (0, 1) using HasFDerivAt.comp_hasDerivAt
       with the embedding (fun y => (x, y)) having derivative (0, 1).
    2. Similarly, ∂f/∂x(p.1, y) = fderiv ℝ f (p.1, y) (1, 0).
    3. Differentiate these w.r.t. x and y respectively using HasDerivAt.clm_apply,
       obtaining fderiv ℝ (fderiv ℝ f) p (1, 0) (0, 1) and (0, 1) (1, 0).
    4. Apply ContDiffAt.isSymmSndFDerivAt for the equality. -/
theorem dd_eq_zero_2D (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ 2 f) (p : ℝ × ℝ) :
    extDeriv1_2D (extDeriv0_2D f) p = 0 := by
  simp only [extDeriv1_2D, extDeriv0_2D]
  rw [sub_eq_zero]
  -- Differentiability: f is C¹, fderiv ℝ f is C¹ (f is C²)
  -- Explicit ℕ∞ type annotations prevent metavar issues in side conditions
  have hDiff : Differentiable ℝ f :=
    hf.differentiable (show (1 : ℕ∞) ≤ 2 by norm_num)
  have hFDiff : Differentiable ℝ (fderiv ℝ f) := by
    have h : ContDiff ℝ 1 (fderiv ℝ f) :=
      hf.fderiv_right (show (1 : ℕ∞) + 1 ≤ 2 by norm_num)
    exact h.differentiable le_rfl
  -- y-partial at (x, p.2): deriv (fun y => f (x, y)) p.2 = fderiv ℝ f (x, p.2) (0, 1)
  have hDY : ∀ x, deriv (fun y => f (x, y)) p.2 = fderiv ℝ f (x, p.2) (0, 1) := fun x =>
    ((hDiff (x, p.2)).hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 x).prod (hasDerivAt_id p.2))
      (show (fun y => (x, y)) p.2 = (x, p.2) from rfl)).deriv
  -- x-partial at (p.1, y): deriv (fun x => f (x, y)) p.1 = fderiv ℝ f (p.1, y) (1, 0)
  have hDX : ∀ y, deriv (fun x => f (x, y)) p.1 = fderiv ℝ f (p.1, y) (1, 0) := fun y =>
    ((hDiff (p.1, y)).hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prod (hasDerivAt_const p.1 y))
      (show (fun x => (x, y)) p.1 = (p.1, y) from rfl)).deriv
  -- Rewrite both sides: the goal becomes about fderiv evaluations
  simp_rw [hDY, hDX]
  -- Second partial: d/dx[fderiv ℝ f (x, p.2)] via chain rule (embedding x ↦ (x, p.2))
  have hStep1 : HasDerivAt (fun x => fderiv ℝ f (x, p.2))
      (fderiv ℝ (fderiv ℝ f) p (1, 0)) p.1 :=
    (hFDiff p).hasFDerivAt.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prod (hasDerivAt_const p.1 p.2)) rfl
  have hStep2 : HasDerivAt (fun y => fderiv ℝ f (p.1, y))
      (fderiv ℝ (fderiv ℝ f) p (0, 1)) p.2 :=
    (hFDiff p).hasFDerivAt.comp_hasDerivAt p.2
      ((hasDerivAt_const p.2 p.1).prod (hasDerivAt_id p.2)) rfl
  -- Apply evaluation via HasDerivAt.clm_apply (product rule: deriv of c(t)(v(t)) = c'(t)(v(t)) + c(t)(v'(t)))
  -- With constant v, v' = 0, so the term (c(t))(v') = 0 and simp handles it
  have hDer2XY : HasDerivAt (fun x => fderiv ℝ f (x, p.2) (0, 1))
      (fderiv ℝ (fderiv ℝ f) p (1, 0) (0, 1)) p.1 := by
    have h := hStep1.clm_apply (hasDerivAt_const p.1 (0, 1 : ℝ × ℝ))
    simp only [map_zero, add_zero] at h; exact h
  have hDer2YX : HasDerivAt (fun y => fderiv ℝ f (p.1, y) (1, 0))
      (fderiv ℝ (fderiv ℝ f) p (0, 1) (1, 0)) p.2 := by
    have h := hStep2.clm_apply (hasDerivAt_const p.2 (1, 0 : ℝ × ℝ))
    simp only [map_zero, add_zero] at h; exact h
  -- Rewrite the goal using the HasDerivAt.deriv identities
  rw [hDer2XY.deriv, hDer2YX.deriv]
  -- Symmetry of the second Fréchet derivative (Clairaut/Schwarz):
  -- ContDiffAt.isSymmSndFDerivAt (hf : ContDiffAt 𝕜 n f x) (hn : minSmoothness 𝕜 2 ≤ n)
  --   : IsSymmSndFDerivAt 𝕜 f x = ∀ v w, fderiv(fderiv f)(x)(v)(w) = fderiv(fderiv f)(x)(w)(v)
  -- minSmoothness ℝ 2 = 2, so le_rfl proves 2 ≤ 2
  exact (hf.contDiffAt.isSymmSndFDerivAt le_rfl) (1, 0) (0, 1)

/-- Green's theorem for rectangles in Stokes form: ∫_{∂R} ω = ∫_R dω.

    This proof uses FTC for both Q (x-direction) and P (y-direction), then
    applies Fubini to exchange the order of integration for the P-term. -/
theorem stokes_2d_rectangle (ω : OneForm2D) (a b c d : ℝ)
    (hQ_deriv : ∀ y, ∀ x ∈ uIcc a b,
      HasDerivAt (fun x => ω.Q (x, y)) (deriv (fun x => ω.Q (x, y)) x) x)
    (hQ_int : ∀ y ∈ uIcc c d,
      IntervalIntegrable (fun x => deriv (fun x => ω.Q (x, y)) x) volume a b)
    (hP_deriv : ∀ x, ∀ y ∈ uIcc c d,
      HasDerivAt (fun y => ω.P (x, y)) (deriv (fun y => ω.P (x, y)) y) y)
    (hP_int : ∀ x ∈ uIcc a b,
      IntervalIntegrable (fun y => deriv (fun y => ω.P (x, y)) y) volume c d)
    (hPdy_x_int : ∀ y ∈ uIcc c d,
      IntervalIntegrable (fun x => deriv (fun y' => ω.P (x, y')) y) volume a b)
    (hFubini : ∫ y in c..d, ∫ x in a..b, deriv (fun y' => ω.P (x, y')) y =
               ∫ x in a..b, ∫ y in c..d, deriv (fun y' => ω.P (x, y')) y) :
    lineIntegralRect ω a b c d =
    areaIntegralRect (extDeriv1_2D ω) a b c d := by
  simp only [lineIntegralRect, areaIntegralRect, extDeriv1_2D]
  -- Apply FTC: ∫_a^b ∂Q/∂x(x, y) dx = Q(b, y) - Q(a, y)
  have hFTC_Q : ∀ y ∈ uIcc c d, ∫ x in a..b, deriv (fun x => ω.Q (x, y)) x =
      ω.Q (b, y) - ω.Q (a, y) := by
    intro y _
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hQ_deriv y x hx) (hQ_int y (by assumption))
  -- Apply FTC: ∫_c^d ∂P/∂y(x, y) dy = P(x, d) - P(x, c)
  have hFTC_P : ∀ x ∈ uIcc a b, ∫ y in c..d, deriv (fun y => ω.P (x, y)) y =
      ω.P (x, d) - ω.P (x, c) := by
    intro x _
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y hy => hP_deriv x y hy) (hP_int x (by assumption))
  -- Transform the area integral via linearity and Fubini
  simp_rw [intervalIntegral.integral_sub (by sorry) (by sorry)]
  -- Use FTC results to rewrite the area integral
  sorry

end GeneralizedStokes
