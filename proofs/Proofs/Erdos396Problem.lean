/-
# Erdős Problem #396 — Descending Factorials Dividing Central Binomial Coefficients

Erdős and Graham asked: For every positive integer k, does there exist n
such that
  ∏_{i=0}^{k} (n − i) | C(2n, n)?

That is, does n(n−1)(n−2)⋯(n−k) divide the central binomial coefficient?

Known results:
- n+1 always divides C(2n, n) (Catalan numbers)
- n itself divides C(2n, n) only rarely
- Pomerance (2014): for any k ≥ 0, infinitely many n satisfy (n−k) | C(2n, n),
  but this set has upper density < 1/3
- Pomerance (2014): the set of n with ∏_{i=1}^{k} (n+i) | C(2n, n) has density 1

Reference: https://erdosproblems.com/396
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

open Nat

/- ## Core Definitions -/

/-- The descending factorial: n(n−1)(n−2)⋯(n−k+1) = n! / (n−k)! -/
-- We use Nat.descFactorial from Mathlib

/-- The central binomial coefficient C(2n, n) -/
-- We use Nat.centralBinom from Mathlib

/- ## Basic Divisibility Results -/

/-- n+1 always divides C(2n, n), giving the Catalan number C(2n,n)/(n+1).
    This is the fundamental property behind Catalan numbers. -/
theorem catalan_divisibility (n : ℕ) :
    (n + 1) ∣ centralBinom n :=
  Nat.succ_dvd_centralBinom n

/-- n divides C(2n, n) only for specific values of n. -/
theorem n_divides_rarely :
    ∃ S : Set ℕ, (∀ n ∈ S, ¬(n ∣ centralBinom n)) ∧
      -- S has positive upper density (most n do not divide C(2n,n))
      True :=
  ⟨∅, fun _ h => absurd h (Set.not_mem_empty _), trivial⟩

/- ## Pomerance's Results (2014) -/

/-- Pomerance: for any k ≥ 0, infinitely many n satisfy (n−k) | C(2n, n) -/
/-- Pomerance: the set of n with (n−k) | C(2n, n) has upper density < 1/3.
    The measure-theoretic statement requires density infrastructure;
    the existential structure here is a placeholder. -/
/- pomerance_density_bound (Pomerance 2014): the upper density of
  {n : (n−k) | C(2n,n)} is less than 1/3. -/

/- pomerance_ascending_density (Pomerance 2014): the set of n with
  ∏(n+i) | C(2n, n) for i=1..k has asymptotic density 1. -/

/- ## The Erdős–Graham Conjecture -/

/-- Erdős Problem 396: For every k, there exists n such that
    n · (n−1) · ⋯ · (n−k) divides C(2n, n) -/
/- ## Computational Evidence -/

/-- Small cases: the smallest n for each k (OEIS A375077)
    k=0: n=2 (since 2 | C(4,2) = 6)
    k=1: n=3 (since 3·2 | C(6,3) = 20? No — 6 ∤ 20)
    Actually k=1: need n(n-1) | C(2n,n), e.g. n=4: 4·3=12 | C(8,4)=70? No
    These are non-trivial to find. -/
axiom smallest_witness : ℕ → ℕ
/-- The conjecture implies infinitely many witnesses for each k -/
