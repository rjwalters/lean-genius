/-
  The Vandermonde determinant and the polynomial identity / interpolation
  uniqueness theorems.

  Over a field `F`, fix `n` DISTINCT nodes `v : Fin n → F`.  The Vandermonde
  matrix `V_{ij} = v_i^j` has nonzero determinant `∏_{i<j}(v_j − v_i) ≠ 0`,
  which makes the evaluation functionals `p ↦ (p(v_0), …, p(v_{n−1}))`
  injective on polynomials of degree `< n`.  Two classical consequences:

    * **Finite identity theorem**: a polynomial of degree `< n` that vanishes at
      `n` distinct points is the zero polynomial;
    * **Interpolation uniqueness**: two polynomials of degree `< n` that agree at
      `n` distinct points are equal — there is at most one interpolant of degree
      `< n` through `n` given points.

  Mathlib proves the *coefficient-vector* form (`vandermonde` det, and
  `eq_zero_of_forall_index_sum_mul_pow_eq_zero`: an injective node set forces a
  vanishing coefficient vector to be zero), but stops short of the
  `Polynomial.eval` bridge.  This file supplies that bridge.  Fully verified: 0
  sorries, 0 axioms, no `native_decide`.
-/
import Mathlib

open Polynomial Matrix Finset

namespace VandermondeInterpolationOQ01

variable {F : Type*} [Field F] {n : ℕ} {v : Fin n → F}

/-- For distinct nodes the Vandermonde determinant is nonzero. -/
theorem vandermonde_det_ne_zero (hv : Function.Injective v) :
    (vandermonde v).det ≠ 0 :=
  det_vandermonde_ne_zero_iff.mpr hv

/-- **Finite identity theorem.** A polynomial of degree `< n` that vanishes at
`n` distinct points is the zero polynomial. -/
theorem eq_zero_of_eval_eq_zero (hv : Function.Injective v) {p : F[X]}
    (hdeg : p.natDegree < n) (hroot : ∀ j, p.eval (v j) = 0) : p = 0 := by
  -- the coefficient vector (restricted to Fin n) is forced to vanish
  have hcoeff : (fun i : Fin n => p.coeff i) = 0 := by
    apply eq_zero_of_forall_index_sum_mul_pow_eq_zero hv
    intro j
    have h := hroot j
    rw [eval_eq_sum_range' hdeg,
      ← Fin.sum_univ_eq_sum_range (fun i => p.coeff i * v j ^ i) n] at h
    exact h
  -- hence every coefficient is zero
  ext k
  rcases lt_or_ge k n with hk | hk
  · simpa using congrFun hcoeff ⟨k, hk⟩
  · simp [coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg hk)]

/-- **Interpolation uniqueness.** Two polynomials of degree `< n` that agree at
`n` distinct points are equal: there is at most one interpolant of degree `< n`
through `n` given values. -/
theorem eq_of_eval_eq (hv : Function.Injective v) {p q : F[X]}
    (hp : p.natDegree < n) (hq : q.natDegree < n)
    (hpq : ∀ j, p.eval (v j) = q.eval (v j)) : p = q := by
  have hdeg : (p - q).natDegree < n :=
    lt_of_le_of_lt (natDegree_sub_le p q) (max_lt hp hq)
  have : p - q = 0 :=
    eq_zero_of_eval_eq_zero hv hdeg fun j => by rw [eval_sub, hpq j, sub_self]
  exact sub_eq_zero.mp this

end VandermondeInterpolationOQ01
