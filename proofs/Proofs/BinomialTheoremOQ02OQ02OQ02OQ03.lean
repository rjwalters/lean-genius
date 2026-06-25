/-
  Figurate (r-simplex) numbers and the general hockey-stick tower
  Open Question: binomial-theorem-oq-02-oq-02-oq-02-oq-03

  The parent BinomialTheoremOQ02OQ02OQ02.lean proves the hockey-stick (Zhu Shijie)
  identity ∑_{m} C(m,r) = C(n+1,r+1) and reads off two *specific* figurate
  consequences: the triangular numbers (r = 2) and the tetrahedral numbers (r = 3).

  Its open question asks for the **figurate generalization to arbitrary r**: read
  the hockey-stick identity as a statement about the whole tower of r-simplex
  (figurate) numbers, of which the line / triangular / tetrahedral numbers are the
  r = 1, 2, 3 floors.

  This file does that. We define the (0-indexed) r-simplex number

      figurate r n := C(n + r, r)

  and prove, with 0 axioms / 0 sorries:

    • figurate_zero/one/two/three : the bottom floors are 1, n+1, the triangular
        numbers (n+1)(n+2)/2, and the tetrahedral numbers (n+1)(n+2)(n+3).
    • figurate_succ_eq_sum  : the **tower** — every (r+1)-simplex number is the
        running total of the r-simplex numbers below it,
            figurate (r+1) n = ∑_{i=0}^{n} figurate r i.
        This is the hockey-stick identity at *arbitrary* r, the generalization the
        parent's two special cases instantiate.
    • figurate_pascal       : the Pascal-style recurrence between adjacent floors,
            figurate (r+1) (n+1) = figurate r (n+1) + figurate (r+1) n.
    • factorial_mul_figurate: the general closed form, r! · figurate r n equals the
        rising factorial (n+1)(n+2)···(n+r).
    • figurate_eq_multichoose: figurate r n = multichoose (n+1) r, identifying the
        figurate numbers with Mathlib's multiset ("stars and bars") count.

  References:
    https://en.wikipedia.org/wiki/Figurate_number
    https://en.wikipedia.org/wiki/Hockey-stick_identity
-/

import Mathlib

namespace BinomialFigurateSimplex

open Finset

/-- **r-simplex (figurate) number**, 0-indexed.

    `figurate r n = C(n + r, r)` counts the points of a discrete r-dimensional
    simplex with `n + 1` points along each edge. The floors of the tower are:
    `r = 0` the constant `1`, `r = 1` the natural numbers, `r = 2` the triangular
    numbers, `r = 3` the tetrahedral numbers, and so on. -/
def figurate (r n : ℕ) : ℕ := (n + r).choose r

/- ## The bottom floors of the tower -/

/-- The 0-simplex numbers are constantly `1` (a single point). -/
@[simp] theorem figurate_zero (n : ℕ) : figurate 0 n = 1 := by
  simp [figurate]

/-- The 1-simplex numbers are the naturals `n + 1` (points on a segment). -/
@[simp] theorem figurate_one (n : ℕ) : figurate 1 n = n + 1 := by
  simp [figurate, Nat.choose_one_right]

/-- The 2-simplex numbers are the triangular numbers `(n+1)(n+2)/2`. -/
theorem figurate_two (n : ℕ) : figurate 2 n = (n + 1) * (n + 2) / 2 := by
  rw [figurate, Nat.choose_two_right]
  rw [show n + 2 - 1 = n + 1 from by omega, Nat.mul_comm]

/-- The 3-simplex numbers are the tetrahedral numbers: `6 · figurate 3 n` is the
    product of three consecutive integers `(n+1)(n+2)(n+3)`. -/
theorem figurate_three (n : ℕ) :
    6 * figurate 3 n = (n + 1) * (n + 2) * (n + 3) := by
  have h : (n + 1).ascFactorial 3 = Nat.factorial 3 * figurate 3 n := by
    rw [figurate, Nat.ascFactorial_eq_factorial_mul_choose]
  have e : (n + 1).ascFactorial 3 = (n + 1) * (n + 2) * (n + 3) := by
    simp only [show (3 : ℕ) = 2 + 1 from rfl, Nat.ascFactorial_succ,
      show (2 : ℕ) = 1 + 1 from rfl, Nat.ascFactorial_succ, Nat.ascFactorial_zero]
    ring
  rw [e, show Nat.factorial 3 = 6 from rfl] at h
  exact h.symm

/- ## The figurate tower: hockey-stick at arbitrary r -/

/-- **The figurate tower.** Each `(r+1)`-simplex number is the running total of
    the `r`-simplex numbers below it:
    `figurate (r+1) n = ∑_{i=0}^{n} figurate r i`.

    This is the hockey-stick (Zhu Shijie) identity stated for *every* `r` at once;
    the triangular (`r = 1`) and tetrahedral (`r = 2`) accumulations the parent file
    derives are the bottom two instances. -/
theorem figurate_succ_eq_sum (r n : ℕ) :
    figurate (r + 1) n = ∑ i ∈ range (n + 1), figurate r i := by
  simp only [figurate]
  rw [Nat.sum_range_add_choose n r, show n + (r + 1) = n + r + 1 from by omega]

/-- **Pascal recurrence between floors.** A figurate number equals the one directly
    below it on the same floor plus the one on the floor beneath:
    `figurate (r+1) (n+1) = figurate r (n+1) + figurate (r+1) n`. -/
theorem figurate_pascal (r n : ℕ) :
    figurate (r + 1) (n + 1) = figurate r (n + 1) + figurate (r + 1) n := by
  simp only [figurate]
  rw [show n + 1 + (r + 1) = (n + r + 1) + 1 from by omega,
      show n + 1 + r = n + r + 1 from by omega,
      show n + (r + 1) = n + r + 1 from by omega,
      Nat.choose_succ_succ (n + r + 1) r]

/- ## Closed forms -/

/-- **General closed form.** `r! · figurate r n` is the rising factorial
    `(n+1)(n+2)···(n+r)`. Dividing by `r!` recovers `figurate r n = C(n+r, r)`,
    and the `r = 2, 3` cases give the triangular and tetrahedral formulas above. -/
theorem factorial_mul_figurate (r n : ℕ) :
    Nat.factorial r * figurate r n = (n + 1).ascFactorial r := by
  rw [figurate, Nat.ascFactorial_eq_factorial_mul_choose]

/-- **Multiset interpretation.** The `r`-simplex numbers are exactly Mathlib's
    `multichoose (n+1) r`: the number of size-`r` multisets drawn from `n+1`
    symbols (the "stars and bars" count). -/
theorem figurate_eq_multichoose (r n : ℕ) :
    figurate r n = Nat.multichoose (n + 1) r := by
  rw [figurate, Nat.multichoose_eq]
  congr 1
  omega

end BinomialFigurateSimplex
