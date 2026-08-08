import Proofs.Erdos85ResiduePartition
import Proofs.Erdos85SquareParameterQuotient

/-!
# Descent inside the square-parameter quotient family

For a realization of the three-component square family, each of the two
short-to-long blocks is a `t`-fold cyclic covering.  Its Gram matrix is
therefore `tI`.  The short--short block of the global second-order identity
then descends to the same identity at the much smaller degree `a=2(k+1)`,
with a single cyclic defect component.

This isolates the genuinely new obstruction: it is enough to rule out the
one-cycle identity at the descended parameters, rather than analyze three
large cycle blocks independently for every `k`.
-/

namespace Erdos85

/-- General minimum-layer block algebra.  If all excursions from a union of
minimum defect components have total Gram matrix `(d-b)I`, restriction of the
degree-`d` boundary identity is again the boundary identity, now at degree
`b`.  This is the algebraic core of the structural descent; it does not depend
on the number or lengths of the longer components. -/
theorem minimumLayer_square_descent
    {S : Type*} [Fintype S] [DecidableEq S]
    (H C J X : Matrix S S ℤ) (d b : ℕ)
    (hsquare : H * H + X =
      ((d : ℤ) - 1) • (1 : Matrix S S ℤ) + J - C)
    (hgram : X = ((d : ℤ) - b) • (1 : Matrix S S ℤ)) :
    H * H = ((b : ℤ) - 1) • (1 : Matrix S S ℤ) + J - C := by
  rw [hgram] at hsquare
  ext x y
  have h := congrFun (congrFun hsquare x) y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul] at h ⊢
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.one_apply_eq, if_pos] at h ⊢
    linear_combination h
  · simp only [Matrix.one_apply, hxy, if_false, mul_zero] at h ⊢
    linear_combination h

/-- Pure block-algebra form of the descent. -/
theorem shortBlock_square_descent
    {S : Type*} [Fintype S] [DecidableEq S]
    (H C J P₁P₁t P₂P₂t : Matrix S S ℤ)
    (d a t : ℕ)
    (hsquare : H * H + P₁P₁t + P₂P₂t =
      ((d : ℤ) - 1) • (1 : Matrix S S ℤ) + J - C)
    (hgram₁ : P₁P₁t = (t : ℤ) • (1 : Matrix S S ℤ))
    (hgram₂ : P₂P₂t = (t : ℤ) • (1 : Matrix S S ℤ))
    (hparam : (d : ℤ) - 1 - 2 * t = (a : ℤ) - 1) :
    H * H = ((a : ℤ) - 1) • (1 : Matrix S S ℤ) + J - C := by
  rw [hgram₁, hgram₂] at hsquare
  ext x y
  have h := congrFun (congrFun hsquare x) y
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul] at h ⊢
  by_cases hxy : x = y
  · subst y
    simp only [Matrix.one_apply_eq, if_pos] at h ⊢
    rw [← hparam]
    linear_combination h
  · simp only [Matrix.one_apply, hxy, if_false, mul_zero] at h ⊢
    linear_combination h

/-- The numerical coefficient in the square family is exactly the descended
degree coefficient. -/
theorem squareFamily_descent_parameter (k : ℕ) :
    (squareFamilyDegree k : ℤ) - 1 -
        2 * (squareFamilyRatio k : ℤ) =
      (2 * (k + 1) : ℕ) - 1 := by
  simp [squareFamilyDegree, squareFamilyRatio]
  ring

/-- Square-family specialization of `shortBlock_square_descent`. -/
theorem squareFamily_shortBlock_square_descent
    {S : Type*} [Fintype S] [DecidableEq S]
    (H C J P₁P₁t P₂P₂t : Matrix S S ℤ) (k : ℕ)
    (hsquare : H * H + P₁P₁t + P₂P₂t =
      ((squareFamilyDegree k : ℤ) - 1) •
          (1 : Matrix S S ℤ) + J - C)
    (hgram₁ : P₁P₁t = (squareFamilyRatio k : ℤ) •
      (1 : Matrix S S ℤ))
    (hgram₂ : P₂P₂t = (squareFamilyRatio k : ℤ) •
      (1 : Matrix S S ℤ)) :
    H * H = ((2 * (k + 1) : ℕ) - 1 : ℤ) •
        (1 : Matrix S S ℤ) + J - C := by
  apply shortBlock_square_descent H C J P₁P₁t P₂P₂t
    (squareFamilyDegree k) (2 * (k + 1)) (squareFamilyRatio k)
    hsquare hgram₁ hgram₂
  exact squareFamily_descent_parameter k

end Erdos85
