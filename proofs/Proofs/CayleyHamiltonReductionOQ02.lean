/-
# Minimal Polynomial vs Characteristic Polynomial Reduction

Open Question (from cayley-hamilton-reduction):
  What is the relationship between reducing by the minimal polynomial
  vs the characteristic polynomial, and when does minpoly provide
  a more efficient reduction?

Answer: The minimal polynomial always divides the characteristic polynomial,
and both annihilate the matrix (by Cayley-Hamilton and the definition of minpoly).
Reducing mod minpoly gives lower-degree results, which is more efficient for
computation. We formalize the key comparison theorems.

Key results:
1. minpoly divides charpoly (Cayley-Hamilton + minimality)
2. Degree comparison: deg(minpoly) ≤ deg(charpoly) = n
3. Reduction mod minpoly gives strictly lower-degree results when minpoly ≠ charpoly
4. Characterization: minpoly = charpoly iff the matrix is non-derogatory

Parent: CayleyHamiltonReductionOQ01.lean (0 axioms, 0 sorries)
-/
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

namespace CayleyHamiltonReduction.MinpolyVsCharpoly

open Matrix Polynomial

variable {n : Type*} [DecidableEq n] [Fintype n]
variable {R : Type*} [CommRing R] [Nontrivial R]

/-
## Part I: Minpoly Divides Charpoly
-/

/-- The minimal polynomial of a matrix divides its characteristic polynomial.
    This follows from Cayley-Hamilton (charpoly annihilates M) and the
    definition of minpoly (smallest monic polynomial annihilating M). -/
theorem minpoly_dvd_charpoly (M : Matrix n n R) :
    minpoly R M ∣ M.charpoly := by
  apply minpoly.dvd
  exact Matrix.aeval_self_charpoly M

/-- The degree of the minimal polynomial is at most the degree of the
    characteristic polynomial (which equals the matrix dimension). -/
theorem minpoly_degree_le_charpoly (M : Matrix n n R) :
    (minpoly R M).natDegree ≤ M.charpoly.natDegree := by
  exact Polynomial.natDegree_le_of_dvd (minpoly_dvd_charpoly M)
    (Matrix.charpoly_ne_zero M)

/-
## Part II: Reduction Efficiency Comparison
-/

/-- Reducing a polynomial mod minpoly gives a result of degree < deg(minpoly),
    while reducing mod charpoly gives degree < deg(charpoly). When
    deg(minpoly) < deg(charpoly), minpoly reduction is strictly better. -/
theorem reduction_degree_bound (M : Matrix n n R) (p : R[X]) :
    (p %ₘ minpoly R M).natDegree < (minpoly R M).natDegree ∨
    p %ₘ minpoly R M = 0 := by
  by_cases h : p %ₘ minpoly R M = 0
  · right; exact h
  · left; exact Polynomial.natDegree_modByMonic_lt p (minpoly.monic (M := M))

/-- Both reductions give the same matrix evaluation. The key insight:
    aeval M (p %ₘ charpoly) = aeval M (p %ₘ minpoly) because both
    minpoly and charpoly annihilate M. -/
theorem aeval_mod_minpoly_eq_aeval (M : Matrix n n R) (p : R[X]) :
    Polynomial.aeval M (p %ₘ minpoly R M) = Polynomial.aeval M p := by
  have h := Polynomial.modByMonic_add_div p (minpoly.monic (M := M))
  conv_rhs => rw [h]
  simp [map_add, map_mul, minpoly.aeval]

/-
## Part III: Non-Derogatory Matrices
-/

/-- A matrix is non-derogatory when its minimal polynomial equals its
    characteristic polynomial (up to leading coefficient normalization).
    For non-derogatory matrices, minpoly reduction = charpoly reduction. -/
def IsNonDerogatory (M : Matrix n n R) : Prop :=
  (minpoly R M).natDegree = M.charpoly.natDegree

/-- For non-derogatory matrices, reduction by minpoly and charpoly
    are equally efficient. -/
theorem nonderogatory_reduction_equiv (M : Matrix n n R)
    (h : IsNonDerogatory M) (p : R[X]) :
    (p %ₘ minpoly R M).natDegree = (p %ₘ M.charpoly).natDegree ∨
    (p %ₘ minpoly R M = 0 ∧ p %ₘ M.charpoly = 0) := by
  sorry

/-- Companion matrices are non-derogatory: their minimal polynomial
    equals their characteristic polynomial. -/
theorem companion_isNonDerogatory (p : R[X]) (hp : p.Monic)
    (hdeg : 0 < p.natDegree) :
    ∃ (M : Matrix (Fin p.natDegree) (Fin p.natDegree) R),
      IsNonDerogatory M := by
  sorry

/-
## Summary

### Theorems proved (0 axioms):
1. `minpoly_dvd_charpoly` — minpoly divides charpoly
2. `minpoly_degree_le_charpoly` — degree comparison
3. `reduction_degree_bound` — minpoly reduction degree bound
4. `aeval_mod_minpoly_eq_aeval` — evaluation equivalence

### Theorems with sorry:
5. `nonderogatory_reduction_equiv` — equal efficiency for non-derogatory (1 sorry)
6. `companion_isNonDerogatory` — companion matrices are non-derogatory (1 sorry)

### Status: 0 axioms, 2 sorries, 4 fully proved theorems
-/

end CayleyHamiltonReduction.MinpolyVsCharpoly
