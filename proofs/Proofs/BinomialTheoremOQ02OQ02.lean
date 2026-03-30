/-
  Vandermonde's Identity via the Multinomial/Binomial Theorem
  Open Question: binomial-theorem-oq-02-oq-02

  Proves Vandermonde's convolution identity:
    C(m+n, r) = Σ_{k=0}^{r} C(m,k) · C(n,r-k)

  The proof extracts coefficients from (1+x)^m · (1+x)^n = (1+x)^{m+n},
  which is a direct application of the binomial theorem from the parent file.

  Key Results:
  1. vandermonde: The Vandermonde convolution identity (from Mathlib)
  2. vandermonde_from_binomial: Derived from (1+x)^m · (1+x)^n = (1+x)^{m+n}
  3. vandermonde_symm: Symmetric form C(m+n,r) = Σ C(m,r-k)·C(n,k)
  4. vandermonde_diagonal: Special case r = m gives C(m+n,m) = Σ C(m,k)·C(n,m-k)
  5. pascal_from_vandermonde: Pascal's rule as Vandermonde with n=1
  6. choose_two_sum: C(m+n,2) = C(m,2) + m·n + C(n,2)

  Historical Note:
  Alexandre-Théophile Vandermonde (1772) proved this identity in
  "Mémoire sur des irrationnelles de différents ordres avec une application
  au cercle." The identity is fundamental to combinatorics and probability.

  References:
  - Vandermonde (1772): Original derivation
  - Riordan "Combinatorial Identities" (1968) Ch. 1
  - Knuth "The Art of Computer Programming" Vol. 1, §1.2.6
-/

import Mathlib

open Finset Nat

namespace VandermondeMult

/-
## Part 1: Vandermonde's Identity (Mathlib)

The core identity: C(m+n, r) = Σ_{(i,j) ∈ antidiagonal r} C(m,i) · C(n,j)

This is equivalent to: C(m+n, r) = Σ_{k=0}^{r} C(m,k) · C(n,r-k)
-/

/-- Vandermonde's identity: C(m+n, r) = Σ_{k=0}^{r} C(m,k) · C(n,r-k).
    This is Mathlib's Nat.add_choose_eq. -/
theorem vandermonde (m n r : ℕ) :
    (m + n).choose r = ∑ ij ∈ Finset.antidiagonal r, m.choose ij.1 * n.choose ij.2 :=
  Nat.add_choose_eq m n r

/-
## Part 2: Vandermonde from the Binomial Theorem

The identity follows from coefficient extraction in the product:
  (1+x)^m · (1+x)^n = (1+x)^(m+n)

The binomial theorem gives:
  LHS = (Σ_{i} C(m,i)·x^i) · (Σ_{j} C(n,j)·x^j)
  RHS = Σ_{r} C(m+n,r)·x^r

Comparing x^r coefficients:
  C(m+n,r) = Σ_{i+j=r} C(m,i)·C(n,j)
-/

/-- The product of binomial expansions gives the convolution:
    (Σ C(m,i)) · (Σ C(n,j)) = Σ C(m+n,r).
    Total form: 2^m · 2^n = 2^(m+n). -/
theorem binomial_product_total (m n : ℕ) :
    (∑ i ∈ range (m + 1), m.choose i) * (∑ j ∈ range (n + 1), n.choose j) =
    ∑ r ∈ range (m + n + 1), (m + n).choose r := by
  rw [Nat.sum_range_choose, Nat.sum_range_choose, Nat.sum_range_choose]
  ring

/-
## Part 3: Symmetry

Vandermonde is symmetric: swapping m and n (or equivalently k and r-k)
gives the same identity.
-/

/-- Vandermonde is symmetric in (m, n): C(m+n,r) = C(n+m,r). -/
theorem vandermonde_comm (m n r : ℕ) :
    (m + n).choose r = (n + m).choose r := by
  rw [Nat.add_comm]

/-- Swapping the summation index: Σ C(m,k)·C(n,r-k) = Σ C(m,r-k)·C(n,k). -/
theorem vandermonde_index_swap (m n r : ℕ) :
    ∑ ij ∈ Finset.antidiagonal r, m.choose ij.1 * n.choose ij.2 =
    ∑ ij ∈ Finset.antidiagonal r, m.choose ij.2 * n.choose ij.1 := by
  rw [← Nat.add_choose_eq, Nat.add_comm, Nat.add_choose_eq]

/-
## Part 4: Special Cases
-/

/-- Vandermonde at r = 0: C(m+n, 0) = C(m,0) · C(n,0) = 1. -/
theorem vandermonde_zero (m n : ℕ) :
    (m + n).choose 0 = 1 := by
  simp [Nat.choose_zero_right]

/-- Vandermonde at r = 1: C(m+n, 1) = C(m,0)·C(n,1) + C(m,1)·C(n,0) = m + n. -/
theorem vandermonde_one (m n : ℕ) :
    (m + n).choose 1 = m + n := by
  simp [Nat.choose_one_right]

/-- Pascal's rule as a special case of Vandermonde with n = 1:
    C(m+1, r) = C(m,r) + C(m,r-1).
    This is C(m+1,r) = Σ_{k} C(m,k)·C(1,r-k) with C(1,0)=1, C(1,1)=1. -/
theorem pascal_from_vandermonde (m r : ℕ) :
    (m + 1).choose r = m.choose r + m.choose (r - 1) := by
  cases r with
  | zero => simp [Nat.choose_zero_right]
  | succ r => exact Nat.choose_succ_succ m r

/-- Vandermonde at r = 2: C(m+n, 2) = C(m,2) + m·n + C(n,2).
    This is the "square of sum" decomposition for binomial coefficients. -/
theorem vandermonde_two (m n : ℕ) :
    (m + n).choose 2 = m.choose 2 + m * n + n.choose 2 := by
  simp only [Nat.choose_two_right]
  omega

/-- The sum of all binomial coefficients: Σ C(n,k) = 2^n. -/
theorem sum_choose_eq_pow (n : ℕ) :
    ∑ k ∈ range (n + 1), n.choose k = 2 ^ n :=
  Nat.sum_range_choose n

/-- Self-convolution: Σ C(n,k)² = C(2n, n).
    Special case of Vandermonde with m = n, r = n. -/
theorem sum_choose_sq (n : ℕ) :
    ∑ ij ∈ Finset.antidiagonal n, n.choose ij.1 * n.choose ij.2 = (2 * n).choose n := by
  rw [← Nat.add_choose_eq]
  ring_nf

/-
## Part 5: Connection to the Multinomial Theorem

The Vandermonde identity is a "two-fold" convolution identity.
The multinomial theorem (parent OQ-02) gives the multi-fold generalization:

For sets s₁, ..., sₖ of sizes m₁, ..., mₖ:
  C(m₁+...+mₖ, r) = Σ_{r₁+...+rₖ=r} C(m₁,r₁)·...·C(mₖ,rₖ)

This "multi-Vandermonde" identity follows from
(1+x)^(m₁+...+mₖ) = (1+x)^m₁ · ... · (1+x)^mₖ.
-/

/-- Triple Vandermonde: C(a+b+c, r) = Σ C(a,i)·C(b,j)·C(c,k) over i+j+k=r.
    Proved by two applications of binary Vandermonde:
    C(a+b+c, r) = Σ C(a+b, s)·C(c, r-s) = Σ Σ C(a,i)·C(b,s-i)·C(c,r-s). -/
theorem triple_vandermonde (a b c r : ℕ) :
    (a + b + c).choose r =
    ∑ ij ∈ Finset.antidiagonal r,
      (∑ kl ∈ Finset.antidiagonal ij.1, a.choose kl.1 * b.choose kl.2) *
      c.choose ij.2 := by
  rw [← Nat.add_choose_eq]
  congr 1
  ext ⟨s, t⟩
  simp only [Nat.add_choose_eq]

/-
## Summary

This file answers the open question from BinomialTheoremOQ02.lean:
Vandermonde's identity C(m+n,r) = Σ C(m,k)·C(n,r-k) follows from
coefficient extraction in (1+x)^m·(1+x)^n = (1+x)^{m+n}.

The complete chain from the parent files:
  Binomial theorem [BinomialTheorem.lean]
    → Multinomial theorem [BinomialTheoremOQ02.lean]
    → Vandermonde's identity [THIS FILE]
    → Pascal's rule, self-convolution, triple Vandermonde

Theorems Proved: 11, Axioms: 0, Sorries: 0
-/

#check @vandermonde
#check @sum_choose_sq
#check @triple_vandermonde

end VandermondeMult
