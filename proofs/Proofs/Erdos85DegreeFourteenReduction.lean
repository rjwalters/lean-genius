import Proofs.Erdos85AdjoinNormMinpoly

/-!
# Reduction of the degree-fourteen boundary to arithmetic certificates

The global orbit argument and defect-cycle localization reduce a hypothetical
degree-`14` graph on `185 = 14 * 13 + 3` vertices to a monic irreducible
factor `f` of a cycle Chebyshev polynomial, with `f(13)` forced to be a
square.  This file packages the exact graph-free arithmetic statement whose
proof remains: every such factor in the range `3 ≤ r ≤ 185` evaluates to a
nonsquare at `13`.
-/

namespace Erdos85

open SimpleGraph Polynomial

noncomputable section

/-- **Degree-fourteen arithmetic reduction.**  If every monic irreducible
factor of every relevant cycle polynomial evaluates to a nonsquare at `13`,
then no `C₄`-free minimum-degree-`14` graph exists at the exact boundary
order `185`.

The arithmetic hypothesis is deliberately stated without reference to a
particular implementation of real cyclotomic polynomials.  The conductor and
executable norm-certificate layers can discharge it independently. -/
theorem false_of_degreeFourteen_cycleFactor_eval_nonsquare
    (harith : ∀ (r : ℕ), 3 ≤ r → r ≤ 185 →
      ∀ f : Polynomial ℚ, f.Monic → Irreducible f →
        f ∣ (Polynomial.Chebyshev.C ℤ (r : ℤ) - 2).map
          (algebraMap ℤ ℚ) →
        ¬ IsSquare (f.eval 13))
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (hmin : 14 ≤ G.minDegree)
    (hcard : Fintype.card V = 185) : False := by
  have hcard' : Fintype.card V = 14 * (14 - 1) + 3 := by
    norm_num [hcard]
  obtain ⟨μ, t, c, r, f, hr3, hrcard, hrle, hf, hmonic, hirr,
      hdvd, htmem, htsq⟩ :=
    exists_boundary_minpoly_factor_with_square
      G hfree (d := 14) (by norm_num) (by decide) hmin hcard'
  have hr185 : r ≤ 185 := by simpa [hcard] using hrle
  have hvalue : ¬ IsSquare ((minpoly ℚ μ).eval 13) := by
    rw [← hf]
    exact harith r hr3 hr185 f hmonic hirr hdvd
  letI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  have hμint : IsIntegral ℚ μ :=
    (Algebra.IsAlgebraic.isAlgebraic μ).isIntegral
  apply not_exists_sq_root_of_minpoly_eval_not_isSquare μ 13 hμint hvalue
  refine ⟨t, htmem, ?_⟩
  norm_num at htsq ⊢
  exact htsq

end

end Erdos85
