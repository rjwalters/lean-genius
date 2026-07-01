import Mathlib

/-
# Uniform Falling-Factorial Closed Forms for the Descending Simplicial Family

## Open Question (combinations-formula-oq-06-oq-02, OQ-02)

The parent entry `combinations-formula-oq-06-oq-02` derived the *ascending* figurate closed
forms uniformly in the dimension `k` from the single identity

  `k ! · S(k, n) = n·(n+1)·⋯·(n+k-1) = ascFactorial n k`,      `S(k, n) = multichoose n k`,

and asked (OQ-02): **can the same `k! · (coefficient) = factorial` engine be pushed to the
falling-factorial `descFactorial` form on the diagonal `(n choose k)`, giving a uniform closed
form for the ascending *and* the descending simplicial families at once?**

## Contribution

Yes — the descending family is the exact mirror of the ascending one, obtained by swapping the
ascending factorial `ascFactorial` for the descending factorial `descFactorial` and the
multiset coefficient `multichoose n k = C(n+k-1, k)` for the ordinary binomial coefficient
`D(k, n) = C(n, k)`.  The engine is the single identity

  `k ! · D(k, n) = n·(n-1)·⋯·(n-k+1) = descFactorial n k`      (`factorial_mul_D`)

which is nothing but the classical `choose ↔ descending-factorial` bridge
(`Nat.descFactorial_eq_factorial_mul_choose`).  It is a *uniform* statement covering the whole
descending tower; its proof is a one-line rewrite, with no per-`k` induction.  The division form

  `D(k, n) = descFactorial n k / k !`                          (`D_closed`)

is its immediate consequence.  Specializing `k` (with natural-number subtraction, honest since
`descFactorial n k = n(n-1)⋯(n-k+1)` truncates to `0` exactly when `k > n`):

* `k = 2`: `2 · D(2, n) = n(n-1)`,          `D(2, n) = n(n-1)/2`
* `k = 3`: `6 · D(3, n) = n(n-1)(n-2)`,     `D(3, n) = n(n-1)(n-2)/6`
* `k = 4`: `24 · D(4, n) = n(n-1)(n-2)(n-3)`, `D(4, n) = n(n-1)(n-2)(n-3)/24`

Placed beside the parent's ascending forms, the two entries exhibit the *same* one-line engine
`k! · coefficient = factorial` producing both simplicial families: the ascending
(rising-factorial, multiset) rungs and the descending (falling-factorial, ordinary binomial)
rungs, with no induction on `n` or `k` anywhere.

## Mathematical Context

`D(k, n) = C(n, k)` counts the `k`-subsets of `{1, …, n}`; the product `n(n-1)⋯(n-k+1)/k!` is
the descending (falling-factorial) form of the binomial coefficient.  Where the ascending
entry read each figurate closed form off `ascFactorial`, this entry reads each descending
closed form off `descFactorial` — the induction that would normally establish each such closed
form is absorbed once and for all into Mathlib's `descFactorial ↔ choose` lemma, exactly
mirroring `combinations-formula-oq-06-oq-02`.
-/

namespace CombinationsFigurateDescClosedForm

open Nat

/-- The descending simplicial coefficient `D(k, n) = C(n, k)`: the number of `k`-subsets of
`{1, …, n}`.  `D(1, n) = n`, `D(2, n)` the "descending triangular" `n(n-1)/2`, etc. -/
def D (k n : ℕ) : ℕ := n.choose k

/-- `D(k, n) = C(n, k)`: definitional restatement, the descending mirror of `S_eq_choose`. -/
theorem D_eq_choose (k n : ℕ) : D k n = n.choose k := rfl

/-- **Uniform falling-factorial closed form.** For every dimension `k`, `k! · D(k, n)` equals
the descending factorial `n(n-1)⋯(n-k+1)`.  A single statement covering the entire descending
simplicial tower; the proof is the `choose ↔ descending-factorial` bridge, no per-`k`
induction.  This is the exact mirror of the parent's `factorial_mul_S`. -/
theorem factorial_mul_D (k n : ℕ) : k ! * D k n = n.descFactorial k := by
  rw [D_eq_choose]
  exact (Nat.descFactorial_eq_factorial_mul_choose n k).symm

/-- **Division form of the uniform closed form:** `D(k, n) = n(n-1)⋯(n-k+1) / k!`, for every
dimension `k` simultaneously. -/
theorem D_closed (k n : ℕ) : D k n = n.descFactorial k / k ! := by
  rw [D_eq_choose]
  rw [eq_comm, Nat.div_eq_iff_eq_mul_left (Nat.factorial_pos k) (Nat.factorial_dvd_descFactorial n k)]
  rw [mul_comm]
  exact Nat.descFactorial_eq_factorial_mul_choose n k

/-!
### Evaluating the finite product `descFactorial n k` at concrete dimensions

Each is three-or-fewer `descFactorial_succ` unfoldings closed by `ring` — no induction. -/

/-- `n(n-1)`: the descending factorial at dimension 2. -/
theorem descFactorial_two (n : ℕ) : n.descFactorial 2 = n * (n - 1) := by
  have h2 : n.descFactorial 2 = (n - 1) * n.descFactorial 1 := Nat.descFactorial_succ n 1
  rw [h2, Nat.descFactorial_one]; ring

/-- `n(n-1)(n-2)`: the descending factorial at dimension 3. -/
theorem descFactorial_three (n : ℕ) : n.descFactorial 3 = n * (n - 1) * (n - 2) := by
  have h3 : n.descFactorial 3 = (n - 2) * n.descFactorial 2 := Nat.descFactorial_succ n 2
  rw [h3, descFactorial_two]; ring

/-- `n(n-1)(n-2)(n-3)`: the descending factorial at dimension 4. -/
theorem descFactorial_four (n : ℕ) :
    n.descFactorial 4 = n * (n - 1) * (n - 2) * (n - 3) := by
  have h4 : n.descFactorial 4 = (n - 3) * n.descFactorial 3 := Nat.descFactorial_succ n 3
  rw [h4, descFactorial_three]; ring

/-!
### Multiplied closed forms (division-free)

The cleanest, most honest statements: no natural-number division truncation is involved. -/

/-- Descending triangular rung: `2 · D(2, n) = n(n-1)`. -/
theorem two_mul_D_two (n : ℕ) : 2 * D 2 n = n * (n - 1) := by
  have h := factorial_mul_D 2 n
  rwa [descFactorial_two, show (2 : ℕ)! = 2 from rfl] at h

/-- Descending tetrahedral rung: `6 · D(3, n) = n(n-1)(n-2)`. -/
theorem six_mul_D_three (n : ℕ) : 6 * D 3 n = n * (n - 1) * (n - 2) := by
  have h := factorial_mul_D 3 n
  rwa [descFactorial_three, show (3 : ℕ)! = 6 from rfl] at h

/-- Descending pentatope rung: `24 · D(4, n) = n(n-1)(n-2)(n-3)`. -/
theorem twentyfour_mul_D_four (n : ℕ) :
    24 * D 4 n = n * (n - 1) * (n - 2) * (n - 3) := by
  have h := factorial_mul_D 4 n
  rwa [descFactorial_four, show (4 : ℕ)! = 24 from rfl] at h

/-!
### Divided closed forms

The familiar textbook shapes, recovered by dividing the multiplied forms. -/

/-- Descending triangular closed form: `D(2, n) = n(n-1)/2`. -/
theorem D_two_closed (n : ℕ) : D 2 n = n * (n - 1) / 2 :=
  Nat.eq_div_of_mul_eq_right (by norm_num) (two_mul_D_two n)

/-- Descending tetrahedral closed form: `D(3, n) = n(n-1)(n-2)/6`. -/
theorem D_three_closed (n : ℕ) : D 3 n = n * (n - 1) * (n - 2) / 6 :=
  Nat.eq_div_of_mul_eq_right (by norm_num) (six_mul_D_three n)

/-- Descending pentatope closed form: `D(4, n) = n(n-1)(n-2)(n-3)/24`. -/
theorem D_four_closed (n : ℕ) : D 4 n = n * (n - 1) * (n - 2) * (n - 3) / 24 :=
  Nat.eq_div_of_mul_eq_right (by norm_num) (twentyfour_mul_D_four n)

/-!
### The `k = 1` base rung and concrete sanity checks -/

/-- Linear rung: `D(1, n) = n`. -/
@[simp] theorem D_one (n : ℕ) : D 1 n = n := Nat.choose_one_right n

/-- `D(k, n) = 0` for `k > n`: the descending family truncates, unlike the ascending one. -/
theorem D_eq_zero_of_lt {k n : ℕ} (h : n < k) : D k n = 0 := Nat.choose_eq_zero_of_lt h

/-- `C(6, 3) = 6·5·4/6 = 20`. -/
example : D 3 6 = 20 := by rw [D_three_closed]

/-- `C(6, 4) = 6·5·4·3/24 = 15`. -/
example : D 4 6 = 15 := by rw [D_four_closed]

/-- `C(5, 2) = 5·4/2 = 10`. -/
example : D 2 5 = 10 := by rw [D_two_closed]

end CombinationsFigurateDescClosedForm
