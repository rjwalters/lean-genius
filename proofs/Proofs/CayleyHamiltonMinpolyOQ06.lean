import Mathlib

/-
# OQ-06: Similar (conjugate) elements share a minimal polynomial

For a unit `u` in any `K`-algebra `A`, conjugation `x ↦ u * x * u⁻¹` is a `K`-algebra
automorphism of `A`, so it preserves the minimal polynomial:

    minpoly K (u * x * u⁻¹) = minpoly K x.

Specialised to `A = Matrix n n K`, this is the classical fact that **similar
matrices** `N = U⁻¹ * M * U` have the same minimal polynomial — the
minimal-polynomial companion of Mathlib's `Matrix.charpoly_units_conj`, which
gives the same statement for the characteristic polynomial.

Everything rests on Mathlib's `minpoly.algEquiv_eq` (the minimal polynomial is
invariant under any `K`-algebra equivalence).  The only new content is packaging
inner conjugation by a unit as such an equivalence (`innerAlgEquiv`).  Note no
integrality hypothesis is needed: the identity holds for every element, integral
or not, because `minpoly.algEquiv_eq` is unconditional.

Sorry-free and axiom-free.
-/

namespace CayleyHamiltonMinpolyOQ06

open Polynomial

variable {K : Type*} [Field K]
variable {A : Type*} [Ring A] [Algebra K A]

/-- Conjugation by a unit `u` of a `K`-algebra `A`, `x ↦ u * x * u⁻¹`, packaged as a
`K`-algebra automorphism of `A`.  Inner automorphisms are the prototypical algebra
automorphisms, and this is the bridge to `minpoly.algEquiv_eq`. -/
def innerAlgEquiv (u : Aˣ) : A ≃ₐ[K] A where
  toFun x := (u : A) * x * (↑u⁻¹ : A)
  invFun x := (↑u⁻¹ : A) * x * (u : A)
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_mul' x y := by simp [mul_assoc]
  map_add' x y := by simp [mul_add, add_mul]
  commutes' r := by
    rw [← Algebra.commutes r (u : A), mul_assoc, Units.mul_inv, mul_one]

@[simp]
theorem innerAlgEquiv_apply (u : Aˣ) (x : A) :
    innerAlgEquiv (K := K) u x = (u : A) * x * (↑u⁻¹ : A) := rfl

/-- **Inner conjugation preserves the minimal polynomial.** For a unit `u` of a
`K`-algebra and any `x`, `u * x * u⁻¹` has the same minimal polynomial as `x`. -/
theorem minpoly_units_conj (u : Aˣ) (x : A) :
    minpoly K ((u : A) * x * (↑u⁻¹ : A)) = minpoly K x := by
  have h := minpoly.algEquiv_eq (innerAlgEquiv (K := K) u) x
  simpa using h

/-- The `u⁻¹ * x * u` form (matching the standard "similar element" presentation
`N = U⁻¹ M U`). -/
theorem minpoly_units_conj' (u : Aˣ) (x : A) :
    minpoly K ((↑u⁻¹ : A) * x * (u : A)) = minpoly K x := by
  have h := minpoly_units_conj (K := K) u⁻¹ x
  simpa using h

/-! ### Matrix specialisation: similar matrices share a minimal polynomial -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Similar matrices share a minimal polynomial.** If `N = U⁻¹ * M * U` for a unit
matrix `U`, then `minpoly K N = minpoly K M`.  This is the minimal-polynomial
analogue of `Matrix.charpoly_units_conj`. -/
theorem minpoly_matrix_units_conj (U : (Matrix n n K)ˣ) (M : Matrix n n K) :
    minpoly K ((↑U⁻¹ : Matrix n n K) * M * (↑U : Matrix n n K)) = minpoly K M :=
  minpoly_units_conj' U M

/-- The `U * M * U⁻¹` form of matrix similarity invariance. -/
theorem minpoly_matrix_units_conj' (U : (Matrix n n K)ˣ) (M : Matrix n n K) :
    minpoly K ((↑U : Matrix n n K) * M * (↑U⁻¹ : Matrix n n K)) = minpoly K M :=
  minpoly_units_conj U M

end CayleyHamiltonMinpolyOQ06
