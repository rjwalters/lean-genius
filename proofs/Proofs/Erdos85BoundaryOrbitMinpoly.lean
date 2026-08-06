import Proofs.Erdos85BoundaryOrbitChebyshev
import Proofs.Erdos85NormSquareBridge

/-!
# The minimal-polynomial form of the boundary square orbit

This packages the selected defect-cycle eigenvalue by its rational minimal
polynomial.  The remaining arithmetic obstruction can therefore be stated
entirely as a finite assertion about monic irreducible factors of mapped
cycle Chebyshev polynomials.
-/

namespace Erdos85

open SimpleGraph Polynomial

noncomputable section

/-- Mapping an integral annihilating polynomial first to `ℚ` and then to the
algebraic closure gives the same evaluation as mapping it directly. -/
theorem aeval_map_rat_eq_eval_map_int
    (P : Polynomial ℤ) (μ : AlgebraicClosure ℚ) :
    Polynomial.aeval μ (P.map (algebraMap ℤ ℚ)) =
      (P.map (algebraMap ℤ (AlgebraicClosure ℚ))).eval μ := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_map,
    ← Polynomial.eval₂_eq_eval_map,
    IsScalarTower.algebraMap_eq ℤ ℚ (AlgebraicClosure ℚ)]

/-- **Minimal-polynomial boundary package.**  The square-carrying defect
eigenvalue has a monic irreducible rational minimal polynomial dividing the
mapped characteristic polynomial of an actual defect cycle. -/
theorem exists_boundary_minpoly_factor_with_square
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {d : ℕ} (hd : 4 ≤ d) (heven : Even d)
    (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3) :
    ∃ (μ t : AlgebraicClosure ℚ)
        (c : (secondOrderDefectGraph G).ConnectedComponent) (r : ℕ)
        (f : Polynomial ℚ),
      3 ≤ r ∧ r = c.supp.ncard ∧ r ≤ Fintype.card V ∧
      f = minpoly ℚ μ ∧ f.Monic ∧ Irreducible f ∧
      f ∣ (Polynomial.Chebyshev.C ℤ (r : ℤ) - 2).map (algebraMap ℤ ℚ) ∧
      t ∈ IntermediateField.adjoin ℚ {μ} ∧
      t * t = (((d : ℚ) - 1 : ℚ) : AlgebraicClosure ℚ) - μ := by
  obtain ⟨μ, t, c, r, hr3, hrcard, hrle, htmem, htsq, hPmonic, hroot⟩ :=
    exists_boundary_cycle_chebyshev_root_with_square
      G hfree hd heven hmin hcard
  let P : Polynomial ℚ :=
    (Polynomial.Chebyshev.C ℤ (r : ℤ) - 2).map (algebraMap ℤ ℚ)
  have hrootQ : Polynomial.aeval μ P = 0 := by
    calc
      Polynomial.aeval μ P =
          ((Polynomial.Chebyshev.C ℤ (r : ℤ) - 2).map
            (algebraMap ℤ (AlgebraicClosure ℚ))).eval μ := by
        exact aeval_map_rat_eq_eval_map_int _ _
      _ = 0 := hroot
  letI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
    AlgebraicClosure.isAlgebraic ℚ
  have hμint : IsIntegral ℚ μ :=
    (Algebra.IsAlgebraic.isAlgebraic μ).isIntegral
  have hfdvd : minpoly ℚ μ ∣ P := minpoly.dvd ℚ μ hrootQ
  exact ⟨μ, t, c, r, minpoly ℚ μ, hr3, hrcard, hrle, rfl,
    minpoly.monic hμint, minpoly.irreducible hμint, hfdvd, htmem, htsq⟩

end

end Erdos85
