/-
  Bézout's identity as a unimodular reduction — the matrix view of the extended Euclidean algorithm
  Open Question: bezout-identity-oq-01-oq-02

  The parent entry (bezout-identity-oq-01) formalizes the extended Euclidean algorithm as a
  computable function `extGcd : ℕ → ℕ → ℤ × ℤ × ℕ` and proves Bézout correctness
  `a·x + b·y = gcd(a,b)` together with the GCD and divisibility corollaries.  Its open question
  asks to *connect the algorithm to matrix arithmetic: the sequence of division steps corresponds
  to a unimodular change of basis.*

  This entry answers that question in closed form.  For integers `a, b` set `g = gcd(a, b)` and let
  `A = gcdA a b`, `B = gcdB a b` be the Bézout coefficients delivered by Mathlib's
  `Int.gcd_eq_gcd_ab` (`g = a·A + b·B`).  Define the 2×2 integer matrix

        U(a,b) = ⎡  A      B  ⎤
                 ⎣ -b/g   a/g ⎦.

  We prove the two facts that make `U` the "matrix form" of the Euclidean algorithm:

    * **Reduction.**  `U ·ᵥ (a, b) = (g, 0)` for *all* `a, b`.  The algorithm's net effect —
      collapsing the input pair to `(gcd, 0)` — is realized by a single linear map, whose top row
      is precisely the Bézout coefficient pair.

    * **Unimodularity.**  When `g ≠ 0`, `det U = 1`, so `U ∈ SL₂(ℤ)`.  Thus the reduction is an
      invertible change of basis over `ℤ`, and the transition from `(a, b)` to `(gcd, 0)` loses no
      information — exactly the structural content behind "the extended Euclidean algorithm is a
      product of elementary unimodular matrices."

  Specializing to a coprime pair (`g = 1`) recovers the classical statement that any primitive
  vector `(a, b)` is carried to the standard basis vector `(1, 0)` by an element of `SL₂(ℤ)` —
  the `n = 2` case of `SL_n(ℤ)` acting transitively on primitive vectors.  As a capstone we package
  `U` as a genuine element of `Matrix.SpecialLinearGroup (Fin 2) ℤ` in the coprime case.

  Everything is derived from Mathlib's `Int.gcdA/gcdB` machinery; no new axioms are introduced.

  References:
  - Bézout, "Théorie générale des équations algébriques" (1779).
  - Mathlib.Data.Int.GCD (`Int.gcd_eq_gcd_ab`, `Int.gcdA`, `Int.gcdB`).
  - Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup (`SL₂(ℤ)`).
  - Parent: BezoutIdentityOQ01.lean (computable `extGcd`).
-/

import Mathlib

namespace BezoutIdentityOQ01OQ02

open Matrix

/-- A convenient entrywise formula for the action of a 2×2 matrix on a length-2 vector. -/
theorem mulVec_two (M : Matrix (Fin 2) (Fin 2) ℤ) (v : Fin 2 → ℤ) :
    M *ᵥ v = ![M 0 0 * v 0 + M 0 1 * v 1, M 1 0 * v 0 + M 1 1 * v 1] := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- The unimodular reduction matrix attached to the extended Euclidean algorithm on `(a, b)`.
Its top row `(gcdA a b, gcdB a b)` is the Bézout coefficient pair; its bottom row `(-b/g, a/g)`
encodes the primitive direction of `(a, b)`. -/
def bezoutMatrix (a b : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![Int.gcdA a b, Int.gcdB a b; -(b / Int.gcd a b), a / Int.gcd a b]

@[simp] theorem bezoutMatrix_zero_zero (a b : ℤ) : bezoutMatrix a b 0 0 = Int.gcdA a b := rfl
@[simp] theorem bezoutMatrix_zero_one (a b : ℤ) : bezoutMatrix a b 0 1 = Int.gcdB a b := rfl
@[simp] theorem bezoutMatrix_one_zero (a b : ℤ) :
    bezoutMatrix a b 1 0 = -(b / Int.gcd a b) := rfl
@[simp] theorem bezoutMatrix_one_one (a b : ℤ) :
    bezoutMatrix a b 1 1 = a / Int.gcd a b := rfl

/-- **Bézout, matrix form.**  The top row of `bezoutMatrix` pairs with `(a, b)` to give `gcd a b`:
this is `Int.gcd_eq_gcd_ab` read off the first coordinate of the reduction. -/
theorem topRow_bezout (a b : ℤ) :
    a * bezoutMatrix a b 0 0 + b * bezoutMatrix a b 0 1 = (Int.gcd a b : ℤ) := by
  simpa using (Int.gcd_eq_gcd_ab a b).symm

/-- **Reduction.**  `U ·ᵥ (a, b) = (gcd a b, 0)` for all integers `a, b`. The extended Euclidean
algorithm's collapse of the pair to `(gcd, 0)` is a single linear map. -/
theorem bezoutMatrix_mulVec (a b : ℤ) :
    bezoutMatrix a b *ᵥ ![a, b] = ![(Int.gcd a b : ℤ), 0] := by
  have hbez : (Int.gcd a b : ℤ) = a * Int.gcdA a b + b * Int.gcdB a b := Int.gcd_eq_gcd_ab a b
  have hda : a / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ) = a :=
    Int.ediv_mul_cancel (Int.gcd_dvd_left a b)
  have hdb : b / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ) = b :=
    Int.ediv_mul_cancel (Int.gcd_dvd_right a b)
  rw [mulVec_two]
  simp only [bezoutMatrix_zero_zero, bezoutMatrix_zero_one, bezoutMatrix_one_zero,
    bezoutMatrix_one_one, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine Matrix.vecCons_inj.mpr ⟨?_, Matrix.vecCons_inj.mpr ⟨?_, rfl⟩⟩
  · -- first coordinate: A·a + B·b = g
    linear_combination -hbez
  · -- second coordinate: (-(b/g))·a + (a/g)·b = 0
    linear_combination (b / (Int.gcd a b : ℤ)) * hda - (a / (Int.gcd a b : ℤ)) * hdb

/-- **Unimodularity.**  When `gcd a b ≠ 0` the reduction matrix has determinant `1`, so it lies in
`SL₂(ℤ)`: the Euclidean reduction is an invertible integral change of basis. -/
theorem bezoutMatrix_det (a b : ℤ) (h : Int.gcd a b ≠ 0) :
    (bezoutMatrix a b).det = 1 := by
  have hg : (Int.gcd a b : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr h
  have hbez : (Int.gcd a b : ℤ) = a * Int.gcdA a b + b * Int.gcdB a b := Int.gcd_eq_gcd_ab a b
  have hda : a / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ) = a :=
    Int.ediv_mul_cancel (Int.gcd_dvd_left a b)
  have hdb : b / (Int.gcd a b : ℤ) * (Int.gcd a b : ℤ) = b :=
    Int.ediv_mul_cancel (Int.gcd_dvd_right a b)
  -- det U = A·(a/g) + B·(b/g); multiply by g and use Bézout to get det U · g = g.
  rw [bezoutMatrix, Matrix.det_fin_two_of]
  have key : ((Int.gcdA a b * (a / (Int.gcd a b : ℤ))
      - Int.gcdB a b * -(b / (Int.gcd a b : ℤ)))) * (Int.gcd a b : ℤ) = (Int.gcd a b : ℤ) := by
    linear_combination Int.gcdA a b * hda + Int.gcdB a b * hdb - hbez
  exact mul_right_cancel₀ hg (by rw [one_mul]; exact key)

/-- The determinant of `bezoutMatrix` is a unit whenever `gcd a b ≠ 0`; equivalently `U` is an
invertible matrix over `ℤ` (an element of `GL₂(ℤ)`). -/
theorem isUnit_bezoutMatrix_det (a b : ℤ) (h : Int.gcd a b ≠ 0) :
    IsUnit (bezoutMatrix a b).det := by
  rw [bezoutMatrix_det a b h]; exact isUnit_one

/-- **Coprime specialization.**  A primitive pair `(a, b)` (i.e. `IsCoprime a b`) is carried to the
standard basis vector `(1, 0)` by the unimodular matrix `U` — the `n = 2` case of `SLₙ(ℤ)` acting
transitively on primitive vectors. -/
theorem bezoutMatrix_mulVec_coprime (a b : ℤ) (h : IsCoprime a b) :
    bezoutMatrix a b *ᵥ ![a, b] = ![1, 0] := by
  have hg : Int.gcd a b = 1 := Int.isCoprime_iff_gcd_eq_one.mp h
  rw [bezoutMatrix_mulVec, hg]; norm_num

theorem bezoutMatrix_det_coprime (a b : ℤ) (h : IsCoprime a b) :
    (bezoutMatrix a b).det = 1 :=
  bezoutMatrix_det a b (by rw [Int.isCoprime_iff_gcd_eq_one.mp h]; exact one_ne_zero)

/-- **Capstone.**  For a coprime pair, `bezoutMatrix` is a genuine element of the special linear
group `SL₂(ℤ)`, carrying `(a, b)` to `(1, 0)`. -/
def bezoutSL (a b : ℤ) (h : IsCoprime a b) : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨bezoutMatrix a b, bezoutMatrix_det_coprime a b h⟩

theorem bezoutSL_mulVec (a b : ℤ) (h : IsCoprime a b) :
    (bezoutSL a b h : Matrix (Fin 2) (Fin 2) ℤ) *ᵥ ![a, b] = ![1, 0] :=
  bezoutMatrix_mulVec_coprime a b h

/-- Sanity check: the reduction of `(12, 8)` is `(gcd 12 8, 0) = (4, 0)`. -/
example : bezoutMatrix 12 8 *ᵥ ![12, 8] = ![4, 0] := by
  rw [bezoutMatrix_mulVec]; norm_num

/-- Sanity check: `(7, 5)` is coprime, so `U` sends it to `(1, 0)`. -/
example : bezoutMatrix 7 5 *ᵥ ![7, 5] = ![1, 0] := by
  rw [bezoutMatrix_mulVec]; norm_num

end BezoutIdentityOQ01OQ02
