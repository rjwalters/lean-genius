/-
  Vandermonde Identity in Falling Factorial Form

  Open Question (arithmetic-series-oq-02-oq-04-oq-01-oq-03):
  "Prove Vandermonde's identity in falling factorial form"

  The falling factorial (descending factorial) of n at r is:
    descFactorial(n, r) = n * (n-1) * ... * (n-r+1)

  The Vandermonde identity in falling factorial form:
    descFactorial(m+n, r) = ∑_{j=0}^{r} C(r, j) * descFactorial(m, j) * descFactorial(n, r-j)

  This generalizes the standard Vandermonde convolution
    C(m+n, r) = ∑_{j=0}^{r} C(m, j) * C(n, r-j)
  by multiplying both sides by r! and using C(n,k)*k! = descFactorial(n,k).

  **Proof**: Convert descFactorial to k!*C(n,k) via Nat.descFactorial_eq_factorial_mul_choose,
  apply the standard Vandermonde (vandermonde_range from BinomialTheoremOQ03),
  then verify each term using the key identity C(r,j)*j!*(r-j)! = r!.

  References:
  - ArithmeticSeriesOQ02OQ04OQ01 for choose_descFactorial
  - BinomialTheoremOQ03 for vandermonde_range
  - Nat.choose_mul_factorial_mul_factorial for key factorial identity
-/
import Mathlib
import Proofs.BinomialTheoremOQ03

open Finset BigOperators

namespace VandermondeDescFactorial

-- ============================================================
-- Section 1: Key Term Equality Lemma
-- ============================================================

/-- For j ≤ r, the j-th term in the falling factorial Vandermonde equals
    r! * C(m,j) * C(n,r-j).
    This is the algebraic core: C(r,j) * j! * (r-j)! = r!. -/
lemma term_eq (m n r j : ℕ) (hj : j ≤ r) :
    Nat.choose r j * (j.factorial * Nat.choose m j) * ((r - j).factorial * Nat.choose n (r - j)) =
    r.factorial * (Nat.choose m j * Nat.choose n (r - j)) := by
  calc Nat.choose r j * (j.factorial * Nat.choose m j) * ((r - j).factorial * Nat.choose n (r - j))
      = (Nat.choose r j * j.factorial * (r - j).factorial) * (Nat.choose m j * Nat.choose n (r - j)) := by ring
    _ = r.factorial * (Nat.choose m j * Nat.choose n (r - j)) := by
        rw [Nat.choose_mul_factorial_mul_factorial hj]

-- ============================================================
-- Section 2: Main Theorem
-- ============================================================

/-- **Vandermonde Identity in Falling Factorial Form**
    (arithmetic-series-oq-02-oq-04-oq-01-oq-03):
    descFactorial(m+n, r) = ∑_{j=0}^{r} C(r,j) * descFactorial(m,j) * descFactorial(n,r-j)

    Proved by converting to binomial form via descFactorial(n,k) = k! * C(n,k),
    applying the standard Vandermonde (from BinomialTheoremOQ03),
    and verifying term equality via C(r,j)*j!*(r-j)! = r!. -/
theorem vandermonde_descFactorial (m n r : ℕ) :
    (m + n).descFactorial r =
    ∑ j ∈ Finset.range (r + 1),
      Nat.choose r j * m.descFactorial j * n.descFactorial (r - j) := by
  -- Convert all descFactorials to factorial * choose
  simp_rw [Nat.descFactorial_eq_factorial_mul_choose]
  -- LHS is now r! * C(m+n, r)
  -- RHS is ∑_j C(r,j) * (j! * C(m,j)) * ((r-j)! * C(n,r-j))
  -- Apply standard Vandermonde: C(m+n,r) = ∑_j C(m,j)*C(n,r-j)
  rw [BinomialTheoremOQ03.vandermonde_range m n r, Finset.mul_sum]
  -- Now both sides are sums over range(r+1)
  -- LHS: ∑_j r! * (C(m,j) * C(n,r-j))
  -- RHS: ∑_j C(r,j) * (j! * C(m,j)) * ((r-j)! * C(n,r-j))
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range, Nat.lt_succ_iff] at hj
  -- Apply term_eq: both sides equal r! * C(m,j) * C(n,r-j)
  exact (term_eq m n r j hj).symm

end VandermondeDescFactorial
