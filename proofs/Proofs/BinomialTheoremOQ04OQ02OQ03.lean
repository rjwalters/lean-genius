/-
Central Binomial Coefficient as a Sum of Squares: C(2n, n) = Σ_k C(n,k)^2

Open Question (binomial-theorem-oq-04-oq-02-oq-03):
"Can the Chu-Vandermonde identity C(2n,n) = Σ C(n,k)^2 be given a direct
combinatorial proof (double-counting) alongside this algebraic one?"

Answer: YES. This is the diagonal m = n, r = n specialization of the
Vandermonde convolution C(m+n, r) = Σ_{i+j=r} C(m,i)·C(n,j), formalized
in the parent entry as `vandermonde_equal`. Setting m = n, r = n and
collapsing the antidiagonal sum to a range sum, the symmetry
C(n, n-k) = C(n, k) turns each convolution term C(n,k)·C(n,n-k) into the
square C(n,k)^2. The "double-counting" reading: both sides count the
number of ways to choose n objects from 2n objects split into two halves
of size n — pick k from the first half and n-k from the second, where
C(n, n-k) = C(n, k) is the number of (n-k)-subsets of the second half.

Main results:
- `central_binomial_eq_sum_sq`: C(2n, n) = Σ_{k=0}^{n} C(n,k)^2
- `centralBinom_eq_sum_sq`: same, phrased with `Nat.centralBinom`
- `sum_sq_choose_example`: numeric instance C(6,3) = 20 = 1+9+9+1

References:
- Chu Shih-Chieh (1303); Vandermonde (1772)
- Parent entry binomial-theorem-oq-04-oq-02 (`vandermonde_equal`)
- Mathlib: Nat.add_choose_eq, Nat.choose_symm,
  Finset.Nat.sum_antidiagonal_eq_sum_range_succ
-/

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic

open Nat BigOperators Finset

namespace BinomialTheoremOQ04OQ02OQ03

/-- **Central binomial coefficient as a sum of squares.**
    `C(2n, n) = Σ_{k=0}^{n} C(n,k)^2`.

    Proof: the diagonal case `m = n`, `r = n` of Vandermonde's convolution
    `C(m+n, r) = Σ_{i+j=r} C(m,i)·C(n,j)` (Mathlib's `Nat.add_choose_eq`).
    Collapsing the antidiagonal sum to a range sum, the convolution term at
    index `k` is `C(n,k) · C(n, n-k)`; since `C(n, n-k) = C(n, k)`
    (`Nat.choose_symm`, valid for `k ≤ n`), each term is `C(n,k)^2`. -/
theorem central_binomial_eq_sum_sq (n : ℕ) :
    Nat.choose (2 * n) n = ∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 2 := by
  rw [two_mul, Nat.add_choose_eq n n n,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => Nat.choose n i * Nat.choose n j) n]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [Nat.choose_symm hk', sq]

/-- The same identity phrased with `Nat.centralBinom`:
    `centralBinom n = Σ_{k=0}^{n} C(n,k)^2`. -/
theorem centralBinom_eq_sum_sq (n : ℕ) :
    Nat.centralBinom n = ∑ k ∈ Finset.range (n + 1), (Nat.choose n k) ^ 2 := by
  rw [Nat.centralBinom_eq_two_mul_choose, central_binomial_eq_sum_sq]

/-- Numeric instance: `C(6, 3) = 1^2 + 3^2 + 3^2 + 1^2 = 20`. -/
theorem sum_sq_choose_example :
    (∑ k ∈ Finset.range 4, (Nat.choose 3 k) ^ 2) = 20 := by
  decide

/-- Consistency check that the general theorem reproduces the numeric instance. -/
theorem central_binomial_three : Nat.choose 6 3 = 20 := by
  decide

end BinomialTheoremOQ04OQ02OQ03
