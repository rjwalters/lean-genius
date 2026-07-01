import Mathlib

/-
# Polynomial Closed Forms for the Hockey-Stick Partial Sums

## Open Question (combinations-formula-oq-06, follow-up)

The parent file `CombinationsFormulaOQ06` proves the hockey-stick identity
`∑_{m≤n} C(m, k) = C(n+1, k+1)` and, at column `k = 1`, the triangular closed form
`C(n+1, 2) = n(n+1)/2`.  It also proves that the sum of the first `n+1` triangular numbers
is the tetrahedral number *as a binomial coefficient* (`sum_triangular_eq_tetrahedral`,
`∑_{m≤n} C(m+1, 2) = C(n+2, 3)`), but leaves that running total in binomial form.

The sibling `combinations-formula-oq-06-oq-02` supplies the *point* closed forms of the
figurate numbers themselves — `C(n+2, 3) = n(n+1)(n+2)/6` and `C(n+3, 4) = …/24` — via the
ascending factorial `S(k, n) = C(n+k-1, k)`.

This entry closes the remaining gap: it gives the **hockey-stick partial sums their own
polynomial closed forms**, and extends the running-total tower one rung further.

  `sum_triangular_closed_form`  — `∑_{m≤n} T_m  = ∑_{m≤n} C(m+1, 2) = n(n+1)(n+2)/6`
  `sum_tetrahedral_eq_pentatope`— `∑_{m≤n} Te_m = ∑_{m≤n} C(m+2, 3) = C(n+3, 4)`  (new rung)
  `sum_tetrahedral_closed_form` — `∑_{m≤n} Te_m = n(n+1)(n+2)(n+3)/24`.

So each simplicial layer is exhibited as the running total of the one beneath it *and* as a
degree-`(k+1)` polynomial in `n`, making the Pythagorean "each layer sums to the next"
picture literal at the level of closed forms.

## Method: the descending factorial, a finite product rather than an induction

The supporting point closed forms are obtained here through the **descending** factorial
(the mirror of the sibling's ascending route), which packages the closed form of every
binomial coefficient without induction on `n`:

  `Nat.descFactorial_eq_factorial_mul_choose : n.descFactorial k = k! * C(n, k)`
  `Nat.descFactorial_eq_prod_range          : n.descFactorial k = ∏_{i<k} (n - i)`.

Chaining them gives, for every dimension `k` at once,

  `k! * C(n+k, k) = ∏_{i<k} (n+k-i)`                        (`figurate_factorial_closed_form`)

a finite product of `k` consecutive integers.  Specialising `k = 3, 4` and evaluating the
short product yields `6·C(n+2, 3) = n(n+1)(n+2)` and `24·C(n+3, 4) = n(n+1)(n+2)(n+3)`; the
partial-sum closed forms then follow by composing the hockey-stick sums with these.

## Axioms: 0 | Sorries: 0
-/

namespace CombinationsFormulaOQ06OQ03

open Finset

/-! ### The hockey-stick identity (restated for self-containment) -/

/-- **Hockey-stick identity (interval form).**  `∑_{m=k}^{n} C(m, k) = C(n+1, k+1)`.
    This is `Nat.sum_Icc_choose`. -/
theorem hockey_stick_Icc (n k : ℕ) :
    ∑ m ∈ Finset.Icc k n, Nat.choose m k = Nat.choose (n + 1) (k + 1) :=
  Nat.sum_Icc_choose n k

/-- **Hockey-stick identity (range form).**  The same sum over `range (n+1)`; extending
    the index range down to `0` changes nothing because `C(m, k) = 0` for `m < k`. -/
theorem hockey_stick_range (n k : ℕ) :
    ∑ m ∈ Finset.range (n + 1), Nat.choose m k = Nat.choose (n + 1) (k + 1) := by
  rw [← hockey_stick_Icc n k]
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_range]
    omega
  · intro m hm hmIcc
    rw [Finset.mem_range] at hm
    rw [Finset.mem_Icc] at hmIcc
    exact Nat.choose_eq_zero_of_lt (by omega)

/-! ### The general induction-free figurate closed form (descending-factorial route) -/

/-- **Figurate closed form (general, no induction).**  For the `k`-dimensional figurate
    number `C(n+k, k)`,

      `k! * C(n+k, k) = ∏_{i<k} (n+k-i)`,

    a finite product of `k` consecutive integers.  Two rewrites from
    `descFactorial = k!·choose` and `descFactorial = ∏ (n - i)`; no recursion on `n`. -/
theorem figurate_factorial_closed_form (n k : ℕ) :
    Nat.factorial k * Nat.choose (n + k) k = ∏ i ∈ Finset.range k, (n + k - i) := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose, Nat.descFactorial_eq_prod_range]

/-! ### Evaluating the short descending factorials -/

/-- The length-3 descending factorial `(n+2)·(n+1)·n`, written low-to-high. -/
theorem descFactorial_three (n : ℕ) :
    (n + 2).descFactorial 3 = n * (n + 1) * (n + 2) := by
  simp only [Nat.descFactorial_eq_prod_range, Finset.prod_range_succ,
    Finset.prod_range_zero, one_mul]
  rw [show n + 2 - 0 = n + 2 from rfl, show n + 2 - 1 = n + 1 from rfl,
    show n + 2 - 2 = n from rfl]
  ring

/-- The length-4 descending factorial `(n+3)·(n+2)·(n+1)·n`, written low-to-high. -/
theorem descFactorial_four (n : ℕ) :
    (n + 3).descFactorial 4 = n * (n + 1) * (n + 2) * (n + 3) := by
  simp only [Nat.descFactorial_eq_prod_range, Finset.prod_range_succ,
    Finset.prod_range_zero, one_mul]
  rw [show n + 3 - 0 = n + 3 from rfl, show n + 3 - 1 = n + 2 from rfl,
    show n + 3 - 2 = n + 1 from rfl, show n + 3 - 3 = n from rfl]
  ring

/-! ### Point closed forms of the tetrahedral and pentatope numbers

These specialise the general identity; they coincide with the sibling entry
`combinations-formula-oq-06-oq-02`'s `S_three_closed` / `S_four_closed` (there `S(k,n) =
C(n+k-1,k)`), and are included here as the supporting lemmas for the partial-sum closed
forms below. -/

/-- `6 · C(n+2, 3) = n(n+1)(n+2)` (division-free), from `descFactorial = 3!·choose`. -/
theorem tetrahedral_mul_closed_form (n : ℕ) :
    6 * Nat.choose (n + 2) 3 = n * (n + 1) * (n + 2) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (n + 2) 3
  rw [descFactorial_three, (by decide : Nat.factorial 3 = 6)] at h
  linarith [h]

/-- `C(n+2, 3) = n(n+1)(n+2)/6`, the tetrahedral point closed form. -/
theorem tetrahedral_closed_form (n : ℕ) :
    Nat.choose (n + 2) 3 = n * (n + 1) * (n + 2) / 6 := by
  have h := tetrahedral_mul_closed_form n
  omega

/-- `24 · C(n+3, 4) = n(n+1)(n+2)(n+3)` (division-free), from `descFactorial = 4!·choose`. -/
theorem pentatope_mul_closed_form (n : ℕ) :
    24 * Nat.choose (n + 3) 4 = n * (n + 1) * (n + 2) * (n + 3) := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (n + 3) 4
  rw [descFactorial_four, (by decide : Nat.factorial 4 = 24)] at h
  linarith [h]

/-- `C(n+3, 4) = n(n+1)(n+2)(n+3)/24`, the pentatope point closed form. -/
theorem pentatope_closed_form (n : ℕ) :
    Nat.choose (n + 3) 4 = n * (n + 1) * (n + 2) * (n + 3) / 24 := by
  have h := pentatope_mul_closed_form n
  omega

/-! ### The main results: polynomial closed forms of the hockey-stick partial sums -/

/-- The sum of the first `n+1` triangular numbers `T_m = C(m+1, 2)` is the tetrahedral
    number `C(n+2, 3)` (hockey-stick, column `2`, dropping the vanishing `C(0,2)` term).
    Restated from the parent as the anchor for its closed form below. -/
theorem sum_triangular_eq_tetrahedral (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), Nat.choose (m + 1) 2 = Nat.choose (n + 2) 3 := by
  have h := hockey_stick_range (n + 1) 2
  rw [Finset.sum_range_succ'] at h
  simpa using h

/-- **Partial-sum closed form (triangular → tetrahedral).**  The running total of the
    triangular numbers is a cubic polynomial in `n`:
    `∑_{m≤n} T_m = n(n+1)(n+2)/6`. -/
theorem sum_triangular_closed_form (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), Nat.choose (m + 1) 2 = n * (n + 1) * (n + 2) / 6 := by
  rw [sum_triangular_eq_tetrahedral, tetrahedral_closed_form]

/-- **New rung.**  The sum of the first `n+1` tetrahedral numbers `Te_m = C(m+2, 3)` is the
    pentatope number `C(n+3, 4)` (hockey-stick, column `3`, dropping the vanishing `C(0,3)`,
    `C(1,3)` terms).  This is the running-total identity one dimension past the parent's. -/
theorem sum_tetrahedral_eq_pentatope (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), Nat.choose (m + 2) 3 = Nat.choose (n + 3) 4 := by
  have h := hockey_stick_range (n + 2) 3
  rw [Finset.sum_range_succ', Finset.sum_range_succ',
    (by decide : Nat.choose 1 3 = 0), (by decide : Nat.choose 0 3 = 0)] at h
  simpa using h

/-- **Partial-sum closed form (tetrahedral → pentatope).**  The running total of the
    tetrahedral numbers is a quartic polynomial in `n`:
    `∑_{m≤n} Te_m = n(n+1)(n+2)(n+3)/24`. -/
theorem sum_tetrahedral_closed_form (n : ℕ) :
    ∑ m ∈ Finset.range (n + 1), Nat.choose (m + 2) 3
      = n * (n + 1) * (n + 2) * (n + 3) / 24 := by
  rw [sum_tetrahedral_eq_pentatope, pentatope_closed_form]

/-! ### Concrete verifications -/

/-- `T_0 + ⋯ + T_4 = 0+1+3+6+10 = 20 = 4·5·6/6` (the `n = 4` triangular running total). -/
example : ∑ m ∈ Finset.range 5, Nat.choose (m + 1) 2 = 4 * 5 * 6 / 6 := by decide
/-- `Te_0 + ⋯ + Te_4 = 0+1+4+10+20 = 35 = C(7, 4) = 4·5·6·7/24`. -/
example : ∑ m ∈ Finset.range 5, Nat.choose (m + 2) 3 = 4 * 5 * 6 * 7 / 24 := by decide
/-- `∑_{m≤4} Te_m = 35 = C(7, 4)`, the running total as a binomial. -/
example : ∑ m ∈ Finset.range 5, Nat.choose (m + 2) 3 = Nat.choose 7 4 := by decide

end CombinationsFormulaOQ06OQ03
