/-
  SL₂ matrix packaging of the Chebyshev addition formulas.

  The parent file (`Proofs.ChebyshevPolynomialsOQ01OQ01`) records the genuine
  angle-addition formulas that Mathlib omits:

  * `T_add`    : `T_{m+n} = T_m·T_n − (1 − X²)·U_{m−1}·U_{n−1}`
                 (the polynomial `cos(α+β) = cos α cos β − sin α sin β`);
  * `U_add`    : `U_{m+n} = U_m·T_n + T_{m+1}·U_{n−1}`
                 (the polynomial `sin(α+β) = sin α cos β + cos α sin β`);
  * `T_sq_add` : `Tₙ² + (1 − X²)·U_{n−1}² = 1` (the Pell / Pythagorean identity).

  This file packages those three scalar identities into a single **structural**
  statement: the assignment

      n ↦ M(n) := !![ Tₙ,        −(1 − X²)·U_{n−1};
                      U_{n−1},    Tₙ ]

  is a **homomorphism from the additive group ℤ into SL₂(R[X])**.  Concretely

  * `chebyMatrix_mul`  : `M(m) · M(n) = M(m+n)` — multiplicativity, which *is* the
                         pair of addition formulas `T_add` / `U_add` read off the
                         four matrix entries;
  * `chebyMatrix_det`  : `det M(n) = 1` — which *is* the Pell identity `T_sq_add`,
                         exhibiting `M(n) ∈ SL₂(R[X])`;
  * `chebyMatrix_zero` : `M(0) = 1` — the group identity.

  These are assembled into `chebyMatrixSL : ℤ → SL₂(R[X])` and the monoid
  homomorphism `chebyMatrixHom : Multiplicative ℤ →* SL₂(R[X])`.  The point is
  that the matrix `M(n)` is the polynomial shadow of the rotation matrix
  `R(nθ) = !![cos nθ, −sin nθ; sin nθ, cos nθ]` (with the metric factor `1 − X²`
  playing the role of `sin² θ`), and the homomorphism property `R(α)R(β)=R(α+β)`
  collapses the cosine and sine addition laws into one `SL₂` identity.

  This is a different object from the scalar parent: it makes the *group*
  structure of the Chebyshev recurrence explicit.  Mathlib has neither the
  Chebyshev matrix nor its `SL₂` packaging.

  Verified: 0 sorries, 0 axioms.
-/
import Mathlib
import Proofs.ChebyshevPolynomialsOQ01OQ01

open Polynomial Matrix

namespace ChebyshevPolynomialsOQ01OQ01OQ01

open Polynomial.Chebyshev ChebyshevPolynomialsOQ01OQ01

variable (R : Type*) [CommRing R]

/-- The **Chebyshev rotation matrix** over `R[X]`:
`M(n) = !![ Tₙ, −(1 − X²)·U_{n−1}; U_{n−1}, Tₙ ]`.

It is the polynomial analogue of the rotation by angle `nθ`,
`!![cos nθ, −sin nθ; sin nθ, cos nθ]`, where `x = cos θ`, `U_{n−1}(x)` stands for
`sin(nθ)/sin θ` and the factor `1 − X²` for `sin² θ`. -/
noncomputable def chebyMatrix (n : ℤ) : Matrix (Fin 2) (Fin 2) R[X] :=
  !![T R n, -(1 - X ^ 2) * U R (n - 1); U R (n - 1), T R n]

/-- **Multiplicativity** of the Chebyshev rotation matrix:
`M(m) · M(n) = M(m+n)`.  The four entry equalities are exactly the first- and
second-kind addition formulas `T_add` and `U_add`; this is the single matrix
identity that contains both. -/
theorem chebyMatrix_mul (m n : ℤ) :
    chebyMatrix R m * chebyMatrix R n = chebyMatrix R (m + n) := by
  have hT := T_add R m n
  have hU := U_add R (m - 1) n
  rw [show m - 1 + n = m + n - 1 from by ring, show m - 1 + 1 = m from by ring] at hU
  have mateq : ∀ a b c d a' b' c' d' : R[X],
      a = a' → b = b' → c = c' → d = d' →
      (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) R[X]) = !![a', b'; c', d'] := by
    rintro a b c d a' b' c' d' rfl rfl rfl rfl; rfl
  simp only [chebyMatrix, Matrix.mul_fin_two]
  rw [hT, hU]
  apply mateq <;> ring

/-- **Determinant** of the Chebyshev rotation matrix is `1`.  This is precisely
the Pell / Pythagorean identity `Tₙ² + (1 − X²)·U_{n−1}² = 1`, so `M(n)` lands in
`SL₂(R[X])`. -/
theorem chebyMatrix_det (n : ℤ) : (chebyMatrix R n).det = 1 := by
  have h := T_sq_add R n
  simp only [chebyMatrix, Matrix.det_fin_two_of]
  linear_combination h

/-- The Chebyshev rotation matrix at `0` is the identity (the group unit). -/
theorem chebyMatrix_zero : chebyMatrix R 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [chebyMatrix, T_zero]

/-- The Chebyshev rotation matrix packaged as an element of `SL₂(R[X])`, using the
determinant computation `chebyMatrix_det`. -/
noncomputable def chebyMatrixSL (n : ℤ) : Matrix.SpecialLinearGroup (Fin 2) R[X] :=
  ⟨chebyMatrix R n, chebyMatrix_det R n⟩

/-- The `SL₂` element at `0` is the identity of the special linear group. -/
theorem chebyMatrixSL_one : chebyMatrixSL R 0 = 1 := by
  apply Subtype.ext
  show chebyMatrix R 0 = ↑(1 : Matrix.SpecialLinearGroup (Fin 2) R[X])
  rw [chebyMatrix_zero, Matrix.SpecialLinearGroup.coe_one]

/-- **Multiplicativity in `SL₂`**: `M(m) · M(n) = M(m+n)` as special linear
matrices. -/
theorem chebyMatrixSL_mul (m n : ℤ) :
    chebyMatrixSL R m * chebyMatrixSL R n = chebyMatrixSL R (m + n) := by
  apply Subtype.ext
  show chebyMatrix R m * chebyMatrix R n = chebyMatrix R (m + n)
  exact chebyMatrix_mul R m n

/-- **The homomorphism** `(ℤ, +) → SL₂(R[X])`, `n ↦ M(n)`.  Its multiplicativity
is the Chebyshev addition formulas and its target `SL₂` is the Pell identity:
the entire angle-addition package is one group homomorphism. -/
noncomputable def chebyMatrixHom : Multiplicative ℤ →* Matrix.SpecialLinearGroup (Fin 2) R[X] where
  toFun n := chebyMatrixSL R (Multiplicative.toAdd n)
  map_one' := chebyMatrixSL_one R
  map_mul' a b := (chebyMatrixSL_mul R a.toAdd b.toAdd).symm

/-! ### Concrete instances -/

/-- The product of the angle-`2` and angle-`3` Chebyshev matrices is the angle-`5`
matrix over `ℤ`: `M(2)·M(3) = M(5)`. -/
example : chebyMatrix ℤ 2 * chebyMatrix ℤ 3 = chebyMatrix ℤ (2 + 3) :=
  chebyMatrix_mul ℤ 2 3

/-- `det M(3) = 1` over `ℤ`: the Pell identity at `n = 3`. -/
example : (chebyMatrix ℤ 3).det = 1 := chebyMatrix_det ℤ 3

end ChebyshevPolynomialsOQ01OQ01OQ01
