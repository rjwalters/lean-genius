import Mathlib

/-!
# Erdős 85: residual characteristic-polynomial irreducibility terminal

The order-49 ordinary-adjacency route produces an even residual polynomial.
If it comes from the square of a rational matrix, its characteristic polynomial
splits into the two positive-degree factors contributed by opposite eigenvalues.
Thus irreducibility of that residual polynomial is already a contradiction.
-/

namespace Erdos85ResidualCharpolyIrreducibilityTerminal

open Polynomial

/-- An irreducible polynomial cannot be expressed as a product of two
positive-degree polynomials.  This is the algebraic endpoint used by the
order-49 residual characteristic-polynomial audit. -/
theorem false_of_irreducible_eq_mul_of_pos_natDegree
    {K : Type*} [Field K] {p q r : K[X]}
    (hp : Irreducible p)
    (hfactor : p = q * r)
    (hq : 0 < q.natDegree)
    (hr : 0 < r.natDegree) : False := by
  rcases hp.isUnit_or_isUnit hfactor with hqunit | hrunit
  · have hzero := Polynomial.natDegree_eq_zero_of_isUnit hqunit
    omega
  · have hzero := Polynomial.natDegree_eq_zero_of_isUnit hrunit
    omega

/-- Contrapositive form convenient for showing that a residual even lift is
reducible once a square-root characteristic polynomial has been constructed. -/
theorem not_irreducible_of_eq_mul_of_pos_natDegree
    {K : Type*} [Field K] {p q r : K[X]}
    (hfactor : p = q * r)
    (hq : 0 < q.natDegree)
    (hr : 0 < r.natDegree) : ¬ Irreducible p := by
  intro hp
  exact false_of_irreducible_eq_mul_of_pos_natDegree hp hfactor hq hr

end Erdos85ResidualCharpolyIrreducibilityTerminal

#print axioms Erdos85ResidualCharpolyIrreducibilityTerminal.false_of_irreducible_eq_mul_of_pos_natDegree
#print axioms Erdos85ResidualCharpolyIrreducibilityTerminal.not_irreducible_of_eq_mul_of_pos_natDegree
