import Mathlib

/-
# Hurwitz square identities are universal commutative-ring identities

Hurwitz's theorem concerns the bilinear `n`-square identities

  (x_1^2 + ... + x_n^2)(y_1^2 + ... + y_n^2) = z_1^2 + ... + z_n^2,    z_i bilinear in x, y,

which exist exactly for `n in {1, 2, 4, 8}` (the dimensions of the four normed
division algebras R, C, H, O).  The gallery entry `hurwitz-theorem-oq-03`
formalizes the *existence* direction over the real numbers `R`, deriving the
4-square identity from Mathlib's quaternion norm.

This file sharpens the existence direction in a different way: the four
identities are not special to `R`.  Each `z_i` is an explicit polynomial with
*integer* coefficients in the `x`'s and `y`'s, so the identity holds **formally
over every commutative ring** -- it is a universal identity, provable by `ring`
over an arbitrary `CommRing R`.

The concrete payoff is purely arithmetic and needs no analysis: in *any*
commutative ring the set of elements expressible as a sum of `1, 2, 4`, or `8`
squares is closed under multiplication.  Specialised to `Z` this is the
multiplicative engine behind the two-square and four-square theorems
(e.g. a product of two sums of four squares is again a sum of four squares).

Everything here is checked by `ring` / elementary `Exists` manipulation:
0 axioms beyond Lean's foundations, 0 sorries.
-/

namespace HurwitzUniversal

open Finset

variable {R : Type*} [CommRing R]

/-- The squared norm (sum of coordinate squares) of an `n`-vector over a
commutative ring. -/
def normSq {n : ℕ} (v : Fin n → R) : R := ∑ i, v i ^ 2

/-! ## The four bilinear multiplications

Each `nMul a b` lists the `n` bilinear components `z_i`.  The coefficients are
the multiplication tables of `R` (`n = 1`), `C` (`n = 2`), `H` (`n = 4`) and
`O` (`n = 8`); identical to the real-valued versions in `HurwitzTheorem`, but
stated here over an arbitrary `R`. -/

/-- `n = 1`: multiplication in `R` itself. -/
def oneMul (a b : Fin 1 → R) : Fin 1 → R := fun _ => a 0 * b 0

/-- `n = 2`: the Brahmagupta–Fibonacci (complex-number) product. -/
def twoMul (a b : Fin 2 → R) : Fin 2 → R :=
  ![a 0 * b 0 - a 1 * b 1,
    a 0 * b 1 + a 1 * b 0]

/-- `n = 4`: Euler's (quaternion) product. -/
def fourMul (a b : Fin 4 → R) : Fin 4 → R :=
  ![a 0 * b 0 - a 1 * b 1 - a 2 * b 2 - a 3 * b 3,
    a 0 * b 1 + a 1 * b 0 + a 2 * b 3 - a 3 * b 2,
    a 0 * b 2 - a 1 * b 3 + a 2 * b 0 + a 3 * b 1,
    a 0 * b 3 + a 1 * b 2 - a 2 * b 1 + a 3 * b 0]

/-- `n = 8`: Degen's (octonion / Cayley–Dickson) product. -/
def eightMul (a b : Fin 8 → R) : Fin 8 → R :=
  ![a 0*b 0 - a 1*b 1 - a 2*b 2 - a 3*b 3 - a 4*b 4 - a 5*b 5 - a 6*b 6 - a 7*b 7,
    a 0*b 1 + a 1*b 0 + a 2*b 3 - a 3*b 2 + a 4*b 5 - a 5*b 4 - a 6*b 7 + a 7*b 6,
    a 0*b 2 - a 1*b 3 + a 2*b 0 + a 3*b 1 + a 4*b 6 + a 5*b 7 - a 6*b 4 - a 7*b 5,
    a 0*b 3 + a 1*b 2 - a 2*b 1 + a 3*b 0 + a 4*b 7 - a 5*b 6 + a 6*b 5 - a 7*b 4,
    a 0*b 4 - a 1*b 5 - a 2*b 6 - a 3*b 7 + a 4*b 0 + a 5*b 1 + a 6*b 2 + a 7*b 3,
    a 0*b 5 + a 1*b 4 - a 2*b 7 + a 3*b 6 - a 4*b 1 + a 5*b 0 - a 6*b 3 + a 7*b 2,
    a 0*b 6 + a 1*b 7 + a 2*b 4 - a 3*b 5 - a 4*b 2 + a 5*b 3 + a 6*b 0 - a 7*b 1,
    a 0*b 7 - a 1*b 6 + a 2*b 5 + a 3*b 4 - a 4*b 3 - a 5*b 2 + a 6*b 1 + a 7*b 0]

/-! ## The universal identities

Each is a single `ring` call after expanding the finite sum and the matrix
literals.  Being a `CommRing`-level identity, it specialises to `Z`, `Q`, `R`,
`C`, `ZMod m`, polynomial rings, etc. -/

/-- `n = 1`: `x^2 * y^2 = (xy)^2` over any commutative ring. -/
theorem one_square (a b : Fin 1 → R) :
    normSq a * normSq b = normSq (oneMul a b) := by
  simp only [normSq, oneMul, Fin.sum_univ_one]
  ring

/-- `n = 2` (Brahmagupta–Fibonacci) over any commutative ring. -/
theorem two_square (a b : Fin 2 → R) :
    normSq a * normSq b = normSq (twoMul a b) := by
  simp only [normSq, twoMul, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

set_option maxHeartbeats 800000 in
/-- `n = 4` (Euler) over any commutative ring. -/
theorem four_square (a b : Fin 4 → R) :
    normSq a * normSq b = normSq (fourMul a b) := by
  simp only [normSq, fourMul, Fin.sum_univ_four, Fin.isValue]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three]
  ring

private lemma sum_fin_eight {f : Fin 8 → R} :
    ∑ i : Fin 8, f i = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  abel

set_option maxHeartbeats 32000000 in
/-- `n = 8` (Degen) over any commutative ring. -/
theorem eight_square (a b : Fin 8 → R) :
    normSq a * normSq b = normSq (eightMul a b) := by
  simp only [normSq, eightMul, sum_fin_eight, Fin.isValue]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.cons_val_three]
  ring

/-! ## Arithmetic consequence: multiplicative closure of sums of squares

`IsSumOfSquares n r` says `r` is a sum of `n` squares in `R`.  For
`n in {1, 2, 4, 8}` the universal identities show this predicate is closed
under multiplication, and it always contains `0` and `1`. -/

/-- `r` is a sum of `n` squares in the commutative ring `R`. -/
def IsSumOfSquares (n : ℕ) (r : R) : Prop := ∃ v : Fin n → R, normSq v = r

theorem isSumOfSquares_zero (n : ℕ) : IsSumOfSquares (R := R) n 0 :=
  ⟨0, by simp [normSq]⟩

theorem isSumOfSquares_one (n : ℕ) [NeZero n] : IsSumOfSquares (R := R) n 1 :=
  ⟨Pi.single ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ 1, by
    simp only [normSq]
    rw [Finset.sum_eq_single ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩]
    · simp
    · intro i _ hi
      rw [Pi.single_eq_of_ne hi]; ring
    · intro h; exact absurd (Finset.mem_univ _) h⟩

/-- Sums of two squares are closed under multiplication (any commutative ring). -/
theorem isSumOfSquares_two_mul {x y : R}
    (hx : IsSumOfSquares 2 x) (hy : IsSumOfSquares 2 y) :
    IsSumOfSquares 2 (x * y) := by
  obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
  exact ⟨twoMul a b, by rw [← two_square, ha, hb]⟩

/-- Sums of four squares are closed under multiplication (any commutative ring). -/
theorem isSumOfSquares_four_mul {x y : R}
    (hx : IsSumOfSquares 4 x) (hy : IsSumOfSquares 4 y) :
    IsSumOfSquares 4 (x * y) := by
  obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
  exact ⟨fourMul a b, by rw [← four_square, ha, hb]⟩

/-- Sums of eight squares are closed under multiplication (any commutative ring). -/
theorem isSumOfSquares_eight_mul {x y : R}
    (hx : IsSumOfSquares 8 x) (hy : IsSumOfSquares 8 y) :
    IsSumOfSquares 8 (x * y) := by
  obtain ⟨a, ha⟩ := hx; obtain ⟨b, hb⟩ := hy
  exact ⟨eightMul a b, by rw [← eight_square, ha, hb]⟩

/-! ## Specialisation to the integers

The closure lemmas are the elementary "easy" direction behind the classical
two-square and four-square theorems. -/

/-- In `Z`, a product of two sums of four squares is a sum of four squares —
the multiplicative step in Lagrange's four-square theorem. -/
theorem int_sumFourSq_mul {x y : ℤ}
    (hx : IsSumOfSquares (R := ℤ) 4 x) (hy : IsSumOfSquares (R := ℤ) 4 y) :
    IsSumOfSquares (R := ℤ) 4 (x * y) :=
  isSumOfSquares_four_mul hx hy

/-- In `Z`, a product of two sums of two squares is a sum of two squares. -/
theorem int_sumTwoSq_mul {x y : ℤ}
    (hx : IsSumOfSquares (R := ℤ) 2 x) (hy : IsSumOfSquares (R := ℤ) 2 y) :
    IsSumOfSquares (R := ℤ) 2 (x * y) :=
  isSumOfSquares_two_mul hx hy

/-- Worked witnesses: `3 = 1^2+1^2+1^2+0^2` and `5 = 2^2+1^2+0^2+0^2`, so the
identity exhibits `15` as a sum of four squares. -/
private lemma three_eq : normSq (R := ℤ) ![1, 1, 1, 0] = 3 := by
  simp only [normSq, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  norm_num

private lemma five_eq : normSq (R := ℤ) ![2, 1, 0, 0] = 5 := by
  simp only [normSq, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three]
  norm_num

example : IsSumOfSquares (R := ℤ) 4 3 := ⟨_, three_eq⟩

example : IsSumOfSquares (R := ℤ) 4 5 := ⟨_, five_eq⟩

example : IsSumOfSquares (R := ℤ) 4 15 :=
  int_sumFourSq_mul ⟨_, three_eq⟩ ⟨_, five_eq⟩

end HurwitzUniversal
