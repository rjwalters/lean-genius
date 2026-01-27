/-
Erdős Problem #397: Products of Central Binomial Coefficients

**Conjecture (Erdős)**: Are there only finitely many solutions to
$$\prod_i \binom{2m_i}{m_i} = \prod_j \binom{2n_j}{n_j}$$
with the $m_i, n_j$ all distinct?

**Answer**: NO - disproved by Somani (2026)

Somani (using ChatGPT) found an infinite family of solutions: for any $a \geq 2$,
if $c = 8a^2 + 8a + 1$, then
$$\binom{2a}{a}\binom{4a+4}{2a+2}\binom{2c}{c} = \binom{2a+2}{a+1}\binom{4a}{2a}\binom{2c+2}{c+1}$$

The $m_i$ values are $\{a, 2a+2, c\}$ and the $n_j$ values are $\{a+1, 2a, c+1\}$,
which are all distinct for $a \geq 2$.

Reference: https://erdosproblems.com/397
-/

import Mathlib

open Nat Finset

namespace Erdos397

/- ## Key Definitions -/

/-- The central binomial coefficient C(2n, n) = (2n)! / (n!)².
    This counts the number of ways to choose n items from 2n items,
    or equivalently, the number of lattice paths from (0,0) to (n,n). -/
abbrev C (n : ℕ) : ℕ := centralBinom n

/-- A solution to the central binomial product equation consists of two
    disjoint finite sets M and N such that ∏_{m ∈ M} C(m) = ∏_{n ∈ N} C(n). -/
def CentralBinomSolutions : Set (Finset ℕ × Finset ℕ) :=
  {p | Disjoint p.1 p.2 ∧ ∏ m ∈ p.1, C m = ∏ n ∈ p.2, C n}

/-- Somani's parameter c(a) = 8a² + 8a + 1 -/
def somaniC (a : ℕ) : ℕ := 8 * a^2 + 8 * a + 1

/- ## Main Result -/

/--
**Erdős Problem #397** (Disproved):

Erdős asked whether there are only finitely many solutions to
∏ᵢ C(2mᵢ, mᵢ) = ∏ⱼ C(2nⱼ, nⱼ) with the mᵢ, nⱼ distinct.

The answer is NO. Somani (2026) showed there are infinitely many solutions
by finding a parametric family: for each a ≥ 2, a solution exists.

We state this as an axiom since the identity verification requires careful
binomial coefficient manipulation beyond straightforward computation.
-/
theorem erdos_397_disproved : CentralBinomSolutions.Infinite := by sorry

/- ## Somani's Infinite Family -/

/-- The left-hand side of Somani's identity: {a, 2a+2, c} -/
def somaniLHS (a : ℕ) : Finset ℕ := {a, 2*a + 2, somaniC a}

/-- The right-hand side of Somani's identity: {a+1, 2a, c+1} -/
def somaniRHS (a : ℕ) : Finset ℕ := {a + 1, 2*a, somaniC a + 1}

/--
Somani's identity: For a ≥ 2, with c = 8a² + 8a + 1,
C(a) · C(2a+2) · C(c) = C(a+1) · C(2a) · C(c+1)

This provides an infinite family of solutions, one for each a ≥ 2.
-/
theorem somani_identity (a : ℕ) (ha : a ≥ 2) :
  C a * C (2*a + 2) * C (somaniC a) = C (a + 1) * C (2*a) * C (somaniC a + 1) := by sorry

/-- For a ≥ 2, the LHS and RHS sets are disjoint -/
theorem somani_disjoint (a : ℕ) (ha : a ≥ 2) : Disjoint (somaniLHS a) (somaniRHS a) := by sorry

/-- Each (somaniLHS a, somaniRHS a) for a ≥ 2 is a valid solution -/
theorem somani_is_solution (a : ℕ) (ha : a ≥ 2) :
    (somaniLHS a, somaniRHS a) ∈ CentralBinomSolutions := by
  constructor
  · exact somani_disjoint a ha
  · -- The equality follows from somani_identity after expanding the products
    simp only [somaniLHS, somaniRHS]
    -- Full proof would unfold the Finset products and apply somani_identity
    sorry

/- ## Basic Properties -/

/-- C(0) = 1 (the central binomial for n=0 is C(0,0) = 1) -/
theorem C_zero : C 0 = 1 := by rfl

/-- C(1) = 2 (the central binomial for n=1 is C(2,1) = 2) -/
theorem C_one : C 1 = 2 := by rfl

/-- C(2) = 6 (the central binomial for n=2 is C(4,2) = 6) -/
theorem C_two : C 2 = 6 := by native_decide

/-- C(3) = 20 (the central binomial for n=3 is C(6,3) = 20) -/
theorem C_three : C 3 = 20 := by native_decide

/-- somaniC(2) = 8·4 + 8·2 + 1 = 49 -/
theorem somaniC_two : somaniC 2 = 49 := by native_decide

end Erdos397
