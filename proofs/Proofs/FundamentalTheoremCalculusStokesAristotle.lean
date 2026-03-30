/-
  Aristotle targets for FundamentalTheoremCalculusStokes
  Routine supporting lemmas for automated proof search.
  See FundamentalTheoremCalculusStokes.lean for the main formalization.

  Criteria for inclusion:
  - d² = 0 (Clairaut's theorem) — well-known calculus result
  - Green's theorem for rectangles — well-known result, full proof exists in GreensTheoremOQ01.lean
  - Clean theorem statements with no definition sorries
  - No axioms, no open conjectures
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

/-- d² = 0 (Clairaut's theorem): mixed partials commute for C² functions. -/
theorem dd_eq_zero_2D (f : ℝ × ℝ → ℝ) (hf : ContDiff ℝ 2 f) (p : ℝ × ℝ) :
    extDeriv1_2D (extDeriv0_2D f) p = 0 := by
  sorry

/-- Green's theorem for rectangles in Stokes form: ∫_{∂R} ω = ∫_R dω. -/
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
  sorry

end GeneralizedStokes
