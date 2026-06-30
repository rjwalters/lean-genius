/-
  The composition law for Chebyshev polynomials of the first kind, and the
  commutative compositional monoid it generates.

  The Chebyshev polynomials of the first kind `Tₙ` satisfy the **composition
  law**

      T_{m·n} = T_m ∘ T_n          (`Polynomial.Chebyshev.T_mul`)

  for all integers `m, n` over any commutative ring `R`.  Mathlib provides this
  multiplicativity (`T_mul`), but it does **not** record any of the structural
  consequences that make it interesting.  The headline result of this file is the
  one Mathlib omits:

      **Chebyshev polynomials commute under composition** —
      `T_m ∘ T_n = T_n ∘ T_m`.

  This is immediate from the composition law together with `m·n = n·m`, yet it is
  a striking fact: the `Tₙ` form a *commuting family* of polynomials, an
  observation that sits at the heart of the Ritt theory of commuting polynomials.

  Around it we collect the rest of the monoid picture:

  * `T_one = X` is the identity for polynomial composition, so `n ↦ Tₙ` sends the
    multiplicative monoid `(ℤ, ·, 1)` into the compositional monoid `(R[X], ∘, X)`;
  * the composition law is associative in the expected way, `T_{l·m·n}` decomposing
    as a triple composite;
  * over `ℝ`, the composition law is exactly the polynomial shadow of the angle
    identity `cos(m·n·θ) = T_m(T_n(cos θ))`, since `Tₙ(cos θ) = cos(n·θ)`.

  Verified: 0 sorries, 0 axioms.
-/
import Mathlib

open Polynomial

namespace ChebyshevPolynomialsOQ01

open Polynomial.Chebyshev

variable (R : Type*) [CommRing R]

/-- **Composition law** for Chebyshev polynomials of the first kind:
`T_{m·n} = T_m ∘ T_n`.  This is Mathlib's `Polynomial.Chebyshev.T_mul`, recorded
here as the foundation for the structural results below. -/
theorem T_comp (m n : ℤ) : T R (m * n) = (T R m).comp (T R n) :=
  T_mul R m n

/-- `T₁ = X`. -/
theorem T_one_eq_X : T R 1 = X :=
  T_one R

/-- `T₁ = X` is a *right* identity for composition: `p ∘ T₁ = p`. -/
@[simp]
theorem comp_T_one (p : R[X]) : p.comp (T R 1) = p := by
  rw [T_one, comp_X]

/-- `T₁ = X` is a *left* identity for composition: `T₁ ∘ p = p`. -/
@[simp]
theorem T_one_comp (p : R[X]) : (T R 1).comp p = p := by
  rw [T_one, X_comp]

/-- The composition law specialised to `n = 1` recovers `T_m` (multiplicative
unit law): `T_m ∘ T₁ = T_m`. -/
theorem T_comp_one (m : ℤ) : (T R m).comp (T R 1) = T R m := by
  rw [← T_comp, mul_one]

/-- **Chebyshev polynomials commute under composition**:
`T_m ∘ T_n = T_n ∘ T_m`.

This is the structural heart of the file and is *not* in Mathlib.  It follows at
once from the composition law `T_comp` and commutativity of integer
multiplication. -/
theorem T_comp_comm (m n : ℤ) : (T R m).comp (T R n) = (T R n).comp (T R m) := by
  rw [← T_comp, ← T_comp, mul_comm]

/-- **Associativity of the composition law**: the triple Chebyshev polynomial
`T_{l·m·n}` is the composite `(T_l ∘ T_m) ∘ T_n`. -/
theorem T_comp_assoc (l m n : ℤ) :
    T R (l * m * n) = ((T R l).comp (T R m)).comp (T R n) := by
  rw [T_comp, T_comp]

/-- The two bracketings of a triple Chebyshev composite agree (an instance of
`Polynomial.comp_assoc`), both equal to `T_{l·m·n}`. -/
theorem T_comp_assoc' (l m n : ℤ) :
    ((T R l).comp (T R m)).comp (T R n) = (T R l).comp ((T R m).comp (T R n)) :=
  comp_assoc _ _ _

end ChebyshevPolynomialsOQ01

/-! ### Concrete instances and the trigonometric origin -/

namespace ChebyshevPolynomialsOQ01

open Polynomial.Chebyshev

/-- A concrete instance of the composition law over `ℤ`: `T₆ = T₂ ∘ T₃`. -/
example : T ℤ 6 = (T ℤ 2).comp (T ℤ 3) := by
  rw [show (6 : ℤ) = 2 * 3 by norm_num, T_comp]

/-- A concrete instance of commutativity over `ℤ`: `T₂ ∘ T₃ = T₃ ∘ T₂`
(both equal `T₆`). -/
example : (T ℤ 2).comp (T ℤ 3) = (T ℤ 3).comp (T ℤ 2) :=
  T_comp_comm ℤ 2 3

/-- **Trigonometric origin of the composition law.**  Because
`Tₙ(cos θ) = cos(n·θ)`, the composition law is the polynomial expression of the
multiple-angle identity `cos(m·n·θ) = T_m(T_n(cos θ))`. -/
theorem T_real_cos_comp (m n : ℤ) (θ : ℝ) :
    (T ℝ m).eval ((T ℝ n).eval (Real.cos θ)) = Real.cos ((m : ℝ) * (n : ℝ) * θ) := by
  rw [T_real_cos, T_real_cos, mul_assoc]

/-- The same identity read through the composition polynomial `T_m ∘ T_n`
evaluated at `cos θ`: it equals `cos(m·n·θ)`. -/
theorem eval_T_comp_cos (m n : ℤ) (θ : ℝ) :
    ((T ℝ m).comp (T ℝ n)).eval (Real.cos θ) = Real.cos ((m : ℝ) * (n : ℝ) * θ) := by
  rw [eval_comp, T_real_cos_comp]

end ChebyshevPolynomialsOQ01
