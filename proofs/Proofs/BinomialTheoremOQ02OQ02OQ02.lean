/-
  The Hockey-Stick (Zhu Shijie) Identity and Figurate Numbers
  Open Question: binomial-theorem-oq-02-oq-02-oq-02

  The parent BinomialTheoremOQ02OQ02.lean proves Vandermonde's convolution
  identity. Its second open question asks:

    "The hockey-stick identity C(r,r) + C(r+1,r) + … + C(n,r) = C(n+1,r+1)
     follows from Vandermonde by a telescoping argument. Can it be derived
     from the existing formalization using `Finset.sum_range_succ` directly?"

  This file answers that directly. It gives a fully self-contained,
  `Finset.sum_range_succ`-based induction proof of the hockey-stick identity
  (the diagonal-sum form ∑_{i≤n} C(r+i, r) = C(r+n+1, r+1)), relates it to
  Mathlib's `Nat.sum_Icc_choose`, and derives the classical figurate-number
  consequences — all with 0 axioms / 0 sorries:

    • `hockeyStick`       : ∑_{i ∈ range (n+1)} C(r+i, r) = C(r+n+1, r+1)
                            (independent induction via sum_range_succ + Pascal).
    • `hockeyStick_Icc`   : ∑_{m ∈ Icc r n} C(m, r) = C(n+1, r+1) (Mathlib form).
    • `sum_Icc_id`        : 1 + 2 + … + n = C(n+1, 2)   (Gauss / triangular).
    • `gauss_sum`         : 1 + 2 + … + n = n(n+1)/2.
    • `sum_Icc_triangular`: ∑_{m≤n} C(m, 2) = C(n+1, 3) (tetrahedral numbers).

  Reference: https://en.wikipedia.org/wiki/Hockey-stick_identity
-/

import Mathlib

namespace BinomialHockeyStick

open Finset

/- ## Part I: The hockey-stick identity, proved by induction -/

/-- **Hockey-stick identity (diagonal form).**
    ∑_{i=0}^{n} C(r+i, r) = C(r+n+1, r+1).

    Proved directly by induction on n with `Finset.sum_range_succ`, peeling off
    the top term and closing each step with Pascal's rule
    `Nat.choose_succ_succ` — the telescoping the parent's OQ#2 describes. -/
theorem hockeyStick (r n : ℕ) :
    ∑ i ∈ range (n + 1), Nat.choose (r + i) r = Nat.choose (r + n + 1) (r + 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    -- Peel off the top term, apply the IH, then close with Pascal's rule.
    rw [Finset.sum_range_succ, ih]
    have e1 : r + (m + 1) = r + m + 1 := by ring
    rw [e1, Nat.choose_succ_succ (r + m + 1) r, Nat.add_comm]

/- ## Part II: Connection to Mathlib's `Icc` form -/

/-- **Hockey-stick identity (interval form).**
    ∑_{m=r}^{n} C(m, r) = C(n+1, r+1). This is Mathlib's `Nat.sum_Icc_choose`,
    restated; together with `hockeyStick` it gives both standard phrasings. -/
theorem hockeyStick_Icc (n r : ℕ) :
    ∑ m ∈ Icc r n, Nat.choose m r = Nat.choose (n + 1) (r + 1) :=
  Nat.sum_Icc_choose n r

/- ## Part III: Figurate-number consequences -/

/-- **Gauss's sum, as a binomial coefficient.** 1 + 2 + … + n = C(n+1, 2).
    Specialize the hockey-stick to r = 1 and use C(m, 1) = m. -/
theorem sum_Icc_id (n : ℕ) :
    ∑ m ∈ Icc 1 n, m = Nat.choose (n + 1) 2 := by
  rw [← hockeyStick_Icc n 1]
  exact Finset.sum_congr rfl (fun m _ => (Nat.choose_one_right m).symm)

/-- **Gauss's sum, closed form.** 1 + 2 + … + n = n(n+1)/2. -/
theorem gauss_sum (n : ℕ) :
    ∑ m ∈ Icc 1 n, m = n * (n + 1) / 2 := by
  rw [sum_Icc_id, Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm (n + 1) n]

/-- **Tetrahedral numbers.** ∑_{m=2}^{n} C(m, 2) = C(n+1, 3): the partial sums
    of the triangular numbers are the tetrahedral numbers. -/
theorem sum_Icc_triangular (n : ℕ) :
    ∑ m ∈ Icc 2 n, Nat.choose m 2 = Nat.choose (n + 1) 3 :=
  Nat.sum_Icc_choose n 2

/-- Sanity check: 1 + 2 + 3 + 4 + 5 = 15 = C(6, 2). -/
example : ∑ m ∈ Icc 1 5, m = 15 := by decide

end BinomialHockeyStick
