import Proofs.Erdos85AdjoinNormMinpoly

/-!
# Reduction of the degree-thirty-four boundary to arithmetic certificates

The global orbit argument and defect-cycle localization reduce a hypothetical
degree-`34` graph on `1125 = 34 * 33 + 3` vertices to a monic irreducible
factor `f` of a cycle Chebyshev polynomial, with `f(33)` forced to be a
square.  This file packages the exact graph-free arithmetic statement whose
proof remains: every such factor in the range `3 ≤ r ≤ 1125` evaluates to a
nonsquare at `33`.
-/

namespace Erdos85

open SimpleGraph Polynomial

noncomputable section

/-- **Degree-thirty-four arithmetic reduction.**  If every monic irreducible
factor of every relevant cycle polynomial evaluates to a nonsquare at `33`,
then no `C₄`-free minimum-degree-`34` graph exists at the exact boundary
order `1125`.

The arithmetic hypothesis is deliberately stated without reference to a
particular implementation of real cyclotomic polynomials.  The conductor and
executable norm-certificate layers can discharge it independently. -/
theorem false_of_degreeThirtyFour_cycleFactor_eval_nonsquare
    (harith : ∀ (r : ℕ), 3 ≤ r → r ≤ 1125 →
      ∀ f : Polynomial ℚ, f.Monic → Irreducible f →
        f ∣ (Polynomial.Chebyshev.C ℤ (r : ℤ) - 2).map
          (algebraMap ℤ ℚ) →
        ¬ IsSquare (f.eval 33))
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : 34 ≤ G.minDegree)
    (hcard : Fintype.card V = 1125) : False := by
  have hcard' : Fintype.card V = 34 * (34 - 1) + 3 := by
    norm_num [hcard]
  obtain ⟨μ, t, c, r, f, hr3, hrcard, hrle, hf, hmonic, hirr,
      hdvd, htmem, htsq⟩ :=
    exists_boundary_minpoly_factor_with_square
      G hfree (d := 34) (by norm_num) (by decide) hmin hcard'
  have hr1125 : r ≤ 1125 := by simpa [hcard] using hrle
  have hvalue : ¬ IsSquare ((minpoly ℚ μ).eval 33) := by
    rw [← hf]
    exact harith r hr3 hr1125 f hmonic hirr hdvd
  letI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  have hμint : IsIntegral ℚ μ :=
    (Algebra.IsAlgebraic.isAlgebraic μ).isIntegral
  apply not_exists_sq_root_of_minpoly_eval_not_isSquare μ 33 hμint hvalue
  refine ⟨t, htmem, ?_⟩
  norm_num at htsq ⊢
  exact htsq

end

end Erdos85
