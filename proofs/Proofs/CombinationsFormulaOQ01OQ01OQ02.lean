/-
p-step shallow diagonals of Pascal's triangle and the p-bonacci sequences
(combinations-formula-oq-01-oq-01-oq-02)

The parent entry `combinations-formula-oq-01-oq-01` proved the classical Fibonacci
shallow-diagonal identity

  `∑_{j} C(n − j, j) = F(n+1)`,

summing binomial coefficients along the shallow (rising) diagonals of Pascal's
triangle.  Its second open question asks to generalize this to the *p-step* shallow
diagonals, which produce the **p-bonacci** (generalized Fibonacci) sequences.

This file answers that question, axiom-free.  Fix a step parameter `q : ℕ`
(so `p = q + 1`) and define the p-step shallow-diagonal sum

  `S q n = ∑_{j} C(n − q·j, j)`.

The main result is that `S q` satisfies the **p-bonacci recurrence**

  `S q (n + q + 1) = S q (n + q) + S q n`          (`pbonacci_rec`)

together with the constant base segment

  `S q n = 1`   for `n ≤ q`                          (`pbonacci_base`).

These two facts characterize `S q` as the generalized Fibonacci sequence of step
`p = q + 1`:

  * `q = 0` (p = 1): the recurrence `S 0 (n+1) = 2·S 0 n` gives the powers of two
    `S 0 n = ∑_j C(n, j) = 2^n`;
  * `q = 1` (p = 2): `S 1 n = F(n+1)`, the Fibonacci numbers — recovering the parent
    result (`pbonacci_one_eq_fib`);
  * `q = 2` (p = 3): `S 2` is Narayana's-cows sequence `a(n) = a(n−1) + a(n−3)`;
  * general `q`: the p-bonacci recurrence `a(n) = a(n−1) + a(n−p)`.

The proof of the recurrence is a single application of Pascal's rule
`C(m+1, k+1) = C(m, k+1) + C(m, k)` to each diagonal term, after peeling the leading
`j = 0` term and reindexing.  The only subtlety is natural-number subtraction
bookkeeping, discharged with `omega` and the vanishing of binomial coefficients past
their support.

Main results:
* `pbonacci`               — the p-step shallow-diagonal sum `∑_j C(n − q·j, j)`.
* `pbonacci_base`          — `S q n = 1` for `n ≤ q` (the constant base segment).
* `pbonacci_rec`           — `S q (n+q+1) = S q (n+q) + S q n` (the p-bonacci recurrence).
* `pbonacci_one_eq_fib`    — `S 1 n = F(n+1)`, recovering the parent Fibonacci identity.
-/

import Mathlib

namespace CombinationsFormulaOQ01OQ01OQ02

open Finset

/-- **The p-step shallow-diagonal sum.** With step parameter `q` (so `p = q + 1`),
sum `C(n − q·j, j)` along the p-step shallow diagonal of Pascal's triangle.  For
`q = 1` this is the Fibonacci diagonal sum `∑_j C(n − j, j)` of the parent entry. -/
def pbonacci (q n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (n + 1), Nat.choose (n - q * j) j

/-- Terms of the diagonal sum vanish once the lower index outruns the upper index,
so the summation range may be enlarged freely above `n`. -/
theorem pbonacci_extend (q n N : ℕ) (h : n ≤ N) :
    ∑ j ∈ Finset.range (N + 1), Nat.choose (n - q * j) j = pbonacci q n := by
  unfold pbonacci
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  · intro j _ hjn
    simp only [Finset.mem_range, not_lt] at hjn
    -- `j ≥ n + 1` forces `n - q*j ≤ n < j`, hence the binomial is zero.
    apply Nat.choose_eq_zero_of_lt
    exact lt_of_le_of_lt (Nat.sub_le n (q * j)) (Nat.lt_of_succ_le hjn)

/-- **Pascal's rule on a diagonal term** (for `j ≥ 1`):
`C(n+q+1 − q(j+1), j+1) = C(n − q·j, j+1) + C(n − q·j, j)`.
This is the engine of the recurrence: the first summand feeds `S q (n+q)`, the second
feeds `S q n`. -/
private theorem diag_pascal (q n j : ℕ) :
    Nat.choose (n + q + 1 - q * (j + 1)) (j + 1)
      = Nat.choose (n - q * j) (j + 1) + Nat.choose (n - q * j) j := by
  rcases le_or_gt (q * (j + 1)) (n + q) with hle | hlt
  · -- No truncation: `n + q + 1 - q(j+1) = (n - q·j) + 1`, plain Pascal.
    have e1 : n + q + 1 - q * (j + 1) = (n - q * j) + 1 := by
      have : q * (j + 1) = q * j + q := by ring
      omega
    rw [e1, Nat.choose_succ_succ, Nat.succ_eq_add_one]
    exact Nat.add_comm _ _
  · -- Truncated case: both upper indices collapse to `0`; here `j ≥ 1`.
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hpos
      · exfalso
        simp only [Nat.zero_add, mul_one] at hlt
        omega
      · exact hpos
    have e1 : n + q + 1 - q * (j + 1) = 0 := by
      have : q * (j + 1) = q * j + q := by ring
      omega
    have e2 : n - q * j = 0 := by
      have h : q * (j + 1) = q * j + q := by ring
      omega
    rw [e1, e2]
    rw [Nat.choose_eq_zero_of_lt (Nat.succ_pos j)]
    rw [Nat.choose_eq_zero_of_lt (show 0 < j by omega)]

/-- **The p-bonacci recurrence.** The p-step shallow-diagonal sums satisfy
`S q (n + q + 1) = S q (n + q) + S q n`, i.e. `a(m) = a(m−1) + a(m−p)` with `p = q+1`. -/
theorem pbonacci_rec (q n : ℕ) :
    pbonacci q (n + q + 1) = pbonacci q (n + q) + pbonacci q n := by
  -- Expand the left side over its natural range and peel the `j = 0` term.
  have hL : pbonacci q (n + q + 1)
      = (∑ j ∈ Finset.range (n + q + 1),
            (Nat.choose (n - q * j) (j + 1) + Nat.choose (n - q * j) j)) + 1 := by
    have hsum : (∑ j ∈ Finset.range (n + q + 1),
          Nat.choose (n + q + 1 - q * (j + 1)) (j + 1))
        = ∑ j ∈ Finset.range (n + q + 1),
            (Nat.choose (n - q * j) (j + 1) + Nat.choose (n - q * j) j) :=
      Finset.sum_congr rfl (fun j _ => diag_pascal q n j)
    unfold pbonacci
    rw [Finset.sum_range_succ', hsum]
    simp
  rw [hL, Finset.sum_add_distrib]
  -- The `C(n - q·j, j)` block over `range (n+q+1)` is `S q n` (extended range).
  have hB : ∑ j ∈ Finset.range (n + q + 1), Nat.choose (n - q * j) j = pbonacci q n :=
    pbonacci_extend q n (n + q) (by omega)
  -- The `C(n - q·j, j+1)` block plus `1` is `S q (n+q)`.
  have hA : (∑ j ∈ Finset.range (n + q + 1), Nat.choose (n - q * j) (j + 1)) + 1
      = pbonacci q (n + q) := by
    -- Expand `S q (n+q)` over its range and peel its `j = 0` term.
    have hexp : pbonacci q (n + q)
        = (∑ j ∈ Finset.range (n + q), Nat.choose (n - q * j) (j + 1)) + 1 := by
      have hsum : (∑ j ∈ Finset.range (n + q), Nat.choose (n + q - q * (j + 1)) (j + 1))
          = ∑ j ∈ Finset.range (n + q), Nat.choose (n - q * j) (j + 1) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        congr 1
        have : q * (j + 1) = q * j + q := by ring
        omega
      unfold pbonacci
      rw [Finset.sum_range_succ', hsum]
      simp
    rw [hexp]
    -- The two `C(n - q·j, j+1)` sums differ only by the `j = n+q` term, which vanishes.
    have htop : ∑ j ∈ Finset.range (n + q + 1), Nat.choose (n - q * j) (j + 1)
        = ∑ j ∈ Finset.range (n + q), Nat.choose (n - q * j) (j + 1) := by
      rw [Finset.sum_range_succ]
      have : Nat.choose (n - q * (n + q)) (n + q + 1) = 0 := by
        apply Nat.choose_eq_zero_of_lt
        have h1 : n - q * (n + q) ≤ n := Nat.sub_le _ _
        omega
      rw [this, Nat.add_zero]
    rw [htop]
  -- `(∑A + ∑B) + 1 = (∑A + 1) + ∑B = S q (n+q) + S q n`.
  omega

/-- **Constant base segment.** For `n ≤ q` the p-step diagonal collapses to its single
leading term: `S q n = 1`.  These are the `p = q+1` initial values of the p-bonacci
sequence. -/
theorem pbonacci_base (q n : ℕ) (h : n ≤ q) : pbonacci q n = 1 := by
  unfold pbonacci
  rw [Finset.sum_range_succ']
  have hzero : ∑ j ∈ Finset.range n, Nat.choose (n - q * (j + 1)) (j + 1) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have e : n - q * (j + 1) = 0 := by
      have : q ≤ q * (j + 1) := by
        calc q = q * 1 := (Nat.mul_one q).symm
          _ ≤ q * (j + 1) := by apply Nat.mul_le_mul_left; omega
      omega
    rw [e]
    exact Nat.choose_eq_zero_of_lt (by omega)
  rw [hzero, Nat.zero_add]
  simp

/-- **Recovering the parent Fibonacci identity.** For step `q = 1` (`p = 2`) the
p-step diagonal sum is the Fibonacci sequence: `S 1 n = F(n+1)`.  Since
`S 1 n = ∑_j C(n − j, j)`, this is exactly the parent's shallow-diagonal identity,
here obtained as a corollary of the general recurrence. -/
theorem pbonacci_one_eq_fib (n : ℕ) : pbonacci 1 n = Nat.fib (n + 1) := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n ih1 ih2 =>
    -- `pbonacci_rec` at `q = 1` gives `S 1 (n+2) = S 1 (n+1) + S 1 n`.
    have hrec : pbonacci 1 (n + 1 + 1) = pbonacci 1 (n + 1) + pbonacci 1 n :=
      pbonacci_rec 1 n
    have hfib : Nat.fib (n + 1 + 1 + 1) = Nat.fib (n + 1 + 1) + Nat.fib (n + 1) := by
      have h := Nat.fib_add_two (n := n + 1)
      rw [Nat.add_comm (Nat.fib (n + 1)) (Nat.fib (n + 1 + 1))] at h
      exact h
    show pbonacci 1 (n + 1 + 1) = Nat.fib (n + 1 + 1 + 1)
    rw [hrec, ih1, ih2, hfib]

end CombinationsFormulaOQ01OQ01OQ02
