/-
  Aristotle targets for Cayley-Hamilton Minpoly OQ-03
  (Computational Complexity of Finding the Minimal Polynomial)

  Routine supporting lemmas for automated proof search.
  See CayleyHamiltonMinpolyOQ03.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture (this is not an open problem)
  - Known results involving polynomial evaluation and mulVec distribution
  - Clean theorem statements with no definition sorries
  - No axioms (all use theorem ... := by sorry)
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Tactic

namespace MinpolyComplexityAristotle

open Matrix Polynomial Finset

variable {K : Type*} [Field K] {n : ℕ}

/-- The k-th Krylov vector: M^k applied to v. -/
def krylovVec (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) (k : ℕ) : Fin n → K :=
  (M ^ k).mulVec v

/-- Polynomial evaluation at a matrix distributes through mulVec as a
    linear combination of Krylov vectors with the polynomial's coefficients.

    This is the key structural lemma connecting aeval to Krylov sequences. -/
theorem aeval_mulVec_eq_krylov_sum (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) (p : K[X]) :
    (aeval M p).mulVec v =
      ∑ i ∈ range (p.natDegree + 1), p.coeff i • krylovVec M v i := by
  sorry

/-- The Krylov vectors {v, Mv, ..., M^d·v} are linearly dependent where
    d = deg(minpoly). The minimal polynomial provides the nontrivial
    dependence relation via its monic leading coefficient. -/
theorem krylov_dependent_at_minpoly_degree [hn : NeZero n]
    (M : Matrix (Fin n) (Fin n) K) (v : Fin n → K) :
    ¬ LinearIndependent K
      (fun i : Fin ((minpoly K M).natDegree + 1) => krylovVec M v i) := by
  sorry

/-- For a nonderogatory matrix (minpoly = charpoly), a cyclic vector
    produces exactly n linearly independent Krylov vectors. -/
theorem nonderogatory_krylov_optimal
    (M : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K)
    (hcyclic : ∀ p : K[X], p.natDegree < n → (aeval M p).mulVec v = 0 → p = 0)
    (hnond : minpoly K M = M.charpoly) :
    LinearIndependent K (fun i : Fin n => krylovVec M v i) := by
  sorry

end MinpolyComplexityAristotle
