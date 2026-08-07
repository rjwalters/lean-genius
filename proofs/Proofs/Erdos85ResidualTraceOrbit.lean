import Proofs.Erdos85OrbitFactorExtraction
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# A nonzero residual trace produces an asymmetric algebraic orbit

After the principal and exceptional rational defect sectors are removed,
the remaining adjacency restriction should have trace zero.  The first half
of that assertion is purely polynomial: if its trace were nonzero, its
characteristic polynomial would have nonzero next-to-leading coefficient,
so it could not be invariant under `X ↦ -X`.  Hence it would contain an
irreducible orbit not fixed by signed reflection.

The graph/operator half can then feed such an orbit into the existing
`AdjoinSquareConjugation` machinery to manufacture another square-carrying
defect orbit, contradicting uniqueness of the exceptional sector.
-/

namespace Erdos85

open Polynomial

noncomputable section

/-- A positive-degree monic rational polynomial with nonzero next
coefficient has an irreducible factor not fixed by signed reflection. -/
theorem Polynomial.exists_asymmetric_irreducible_of_nextCoeff_ne_zero
    (q : Polynomial ℚ) (hq : q.Monic) (hdeg : 0 < q.natDegree)
    (hnext : q.nextCoeff ≠ 0) :
    ∃ f : Polynomial ℚ,
      Irreducible f ∧ f.Monic ∧ f ∣ q ∧ signedReflection f ≠ f := by
  apply exists_irreducible_dvd_not_reflection_fixed_of_not_signStable q hq
  intro hsign
  have hz := coeff_natDegree_sub_one_eq_zero_of_signStable q hdeg hsign
  rw [← Polynomial.nextCoeff_of_natDegree_pos hdeg] at hz
  exact hnext hz

/-- **Residual trace-to-orbit interface.**  Every nonzero matrix trace on a
nontrivial rational coordinate space produces an asymmetric irreducible
factor of its characteristic polynomial. -/
theorem Matrix.exists_asymmetric_charpoly_factor_of_trace_ne_zero
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (M : Matrix I I ℚ) (htrace : Matrix.trace M ≠ 0) :
    ∃ f : Polynomial ℚ,
      Irreducible f ∧ f.Monic ∧ f ∣ M.charpoly ∧
        Polynomial.signedReflection f ≠ f := by
  have hdeg : 0 < M.charpoly.natDegree := by
    rw [Matrix.charpoly_natDegree_eq_dim]
    exact Fintype.card_pos
  have hnext : M.charpoly.nextCoeff ≠ 0 := by
    have ht := Matrix.trace_eq_neg_charpoly_nextCoeff M
    intro hn
    apply htrace
    rw [hn] at ht
    simpa using ht
  exact Polynomial.exists_asymmetric_irreducible_of_nextCoeff_ne_zero
    M.charpoly (Matrix.charpoly_monic M) hdeg hnext

end

end Erdos85
