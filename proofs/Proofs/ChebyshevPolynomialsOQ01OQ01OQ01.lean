/-
  SL₂ matrix packaging of the Chebyshev addition formulas.

  The parent file `Proofs.ChebyshevPolynomialsOQ01OQ01` proves the scalar
  angle-addition identities for the Chebyshev polynomials:

    * `T_add`    : T_{m+n} = T_m·T_n − (1−X²)·U_{m−1}·U_{n−1}
    * `U_add`    : U_{m+n} = U_m·T_n + T_{m+1}·U_{n−1}
    * `T_sq_add` : Tₙ² + (1−X²)·U_{n−1}² = 1   (Pell / cos²+sin²=1)

  This file answers the parent's first open question by packaging all three
  into a *single* statement: the 2×2 matrix

      M(n) = !![ Tₙ      , −(1−X²)·U_{n−1} ;
                 U_{n−1} ,  Tₙ            ]

  -- the polynomial shadow of the rotation matrix
  `R(nθ) = !![cos nθ, −sin nθ; sin nθ, cos nθ]`, with `cos nθ = Tₙ(x)` and
  `sin nθ = sin θ · U_{n−1}(x)` (so the common `sin θ` scaling of the off-diagonal
  row and column cancels and leaves the factor `1 − x² = sin²θ` in one corner) --
  defines a *monoid homomorphism* `(ℤ, +) → SL₂(R[X])`:

    * `chebMat_zero` : M(0) = 1                       (T₀ = 1, U_{−1} = 0)
    * `chebMat_mul`  : M(m+n) = M(m)·M(n)             (T_add ∧ U_add at once)
    * `chebMat_det`  : det M(n) = 1                   (the Pell identity)

  so each `M(n) ∈ SL₂(R[X])`, and multiplicativity of the determinant makes the
  Pell identity `det M(n) = (det M(1))ⁿ = 1` an automatic consequence.  Finally

    * `chebMat_pow`      : M(↑n) = M(1)ⁿ   for `n : ℕ`,
    * `chebMat_one`      : M(1) = !![X, −(1−X²); 1, X],
    * `cheb_pow_entry_T` : (M(1)ⁿ) 0 0 = Tₙ,
    * `cheb_pow_entry_U` : (M(1)ⁿ) 1 0 = U_{n−1},

  exhibit `T` and `U` as the matrix entries of the powers of the single
  "Chebyshev rotation" `M(1)`, exactly as the powers of `!![1,1;1,0]` generate the
  Fibonacci numbers.  Mathlib records `T`, `U` and their recurrences, but not this
  SL₂ packaging.

  Verified: 0 sorries, 0 axioms.
-/
import Mathlib
import Proofs.ChebyshevPolynomialsOQ01OQ01

open Polynomial Matrix Polynomial.Chebyshev

namespace ChebyshevPolynomialsOQ01OQ01OQ01

variable (R : Type*) [CommRing R]

/-- Entrywise equality of `2×2` matrix literals: reduces a matrix equation to its
four scalar entries (so each can be discharged by `ring`). -/
private theorem mat2_ext {α : Type*} (a b c d a' b' c' d' : α)
    (h00 : a = a') (h01 : b = b') (h10 : c = c') (h11 : d = d') :
    !![a, b; c, d] = !![a', b'; c', d'] := by
  rw [h00, h01, h10, h11]

/-- The **Chebyshev SL₂ matrix** `M(n) = !![Tₙ, −(1−X²)·U_{n−1}; U_{n−1}, Tₙ]`,
the polynomial shadow of the rotation `!![cos nθ, −sin nθ; sin nθ, cos nθ]`. -/
noncomputable def chebMat (n : ℤ) : Matrix (Fin 2) (Fin 2) R[X] :=
  !![T R n, -((1 - X ^ 2) * U R (n - 1)); U R (n - 1), T R n]

/-- `M(0) = 1`: the identity matrix, since `T₀ = 1` and `U_{−1} = 0`. -/
theorem chebMat_zero : chebMat R 0 = 1 := by
  simp only [chebMat, show (0 : ℤ) - 1 = -1 from by ring, T_zero, U_neg_one,
    mul_zero, neg_zero, Matrix.one_fin_two]

/-- `M(1) = !![X, −(1−X²); 1, X]`, since `T₁ = X` and `U₀ = 1`. This single matrix
is the "Chebyshev rotation" whose powers generate the whole `T`/`U` family. -/
theorem chebMat_one : chebMat R 1 = !![X, -(1 - X ^ 2); 1, X] := by
  simp only [chebMat, show (1 : ℤ) - 1 = 0 from by ring, T_one, U_zero, mul_one]

/-- **Multiplicativity** `M(m+n) = M(m)·M(n)`: the `(0,0)`/`(1,1)` entries are the
first-kind addition formula `T_add`, and the `(1,0)`/`(0,1)` entries are the
second-kind addition formula `U_add`. The two scalar identities are packaged here
as one matrix product. -/
theorem chebMat_mul (m n : ℤ) : chebMat R (m + n) = chebMat R m * chebMat R n := by
  have hT := ChebyshevPolynomialsOQ01OQ01.T_add R m n
  have hU := ChebyshevPolynomialsOQ01OQ01.U_add R (m - 1) n
  rw [show m - 1 + n = m + n - 1 from by ring, show m - 1 + 1 = m from by ring] at hU
  simp only [chebMat, Matrix.mul_fin_two]
  exact mat2_ext _ _ _ _ _ _ _ _
    (by simp only [hT]; ring) (by simp only [hU]; ring)
    (by rw [hU]) (by simp only [hT]; ring)

/-- **Determinant** `det M(n) = 1`: this is exactly the Pell / Pythagorean identity
`Tₙ² + (1−X²)·U_{n−1}² = 1`, so every `M(n)` lies in `SL₂(R[X])`. -/
theorem chebMat_det (n : ℤ) : (chebMat R n).det = 1 := by
  rw [chebMat, Matrix.det_fin_two_of]
  linear_combination ChebyshevPolynomialsOQ01OQ01.T_sq_add R n

/-- The matrices are the powers of the single rotation `M(1)`: `M(↑n) = M(1)ⁿ`.
Proved by induction from `chebMat_zero` and `chebMat_mul`. -/
theorem chebMat_pow (n : ℕ) : chebMat R (n : ℤ) = chebMat R 1 ^ n := by
  induction n with
  | zero => simpa using chebMat_zero R
  | succ k ih =>
      rw [pow_succ, ← ih, ← chebMat_mul R (k : ℤ) 1, Nat.cast_succ]

/-- The first-kind polynomial `Tₙ` is the top-left entry of `M(1)ⁿ`. -/
theorem cheb_pow_entry_T (n : ℕ) : (chebMat R 1 ^ n) 0 0 = T R (n : ℤ) := by
  rw [← chebMat_pow]
  simp [chebMat]

/-- The second-kind polynomial `U_{n−1}` is the bottom-left entry of `M(1)ⁿ`. -/
theorem cheb_pow_entry_U (n : ℕ) : (chebMat R 1 ^ n) 1 0 = U R ((n : ℤ) - 1) := by
  rw [← chebMat_pow]
  simp [chebMat]

/-! ### Concrete instances -/

/-- Multiplicativity at `m = 2, n = 3` over `ℤ`. -/
example : chebMat ℤ (2 + 3) = chebMat ℤ 2 * chebMat ℤ 3 := chebMat_mul ℤ 2 3

/-- Each Chebyshev matrix lands in `SL₂`: `det = 1` at `n = 4` over `ℤ`. -/
example : (chebMat ℤ 4).det = 1 := chebMat_det ℤ 4

/-- `T₃` is the `(0,0)` entry of the cube of the Chebyshev rotation `M(1)` over `ℤ`. -/
example : (chebMat ℤ 1 ^ 3) 0 0 = T ℤ 3 := cheb_pow_entry_T ℤ 3

end ChebyshevPolynomialsOQ01OQ01OQ01
