/-
Erdős Problem #727: Factorial Divisibility

For k ≥ 2, does ((n+k)!)² | (2n)! for infinitely many n?

**Status**: OPEN (for k ≥ 2)

**Background**:
- Conjecture of Erdős, Graham, Ruzsa, and Straus (1975)
- It is open even for k = 2
- Balakran (1929) proved the k = 1 case: ((n+1)!)² | (2n)! for infinitely many n
- Classical fact: (n+1) | C(2n,n) for all n (Catalan numbers)
- EGRS showed: (n+k)!(n+1)! | (2n)! for infinitely many n (any k ≥ 2)

Reference: https://erdosproblems.com/727
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Nat Set

namespace Erdos727

/-!
## Background: Factorials and Divisibility

The central binomial coefficient C(2n, n) = (2n)! / (n!)² has many divisibility
properties. This problem explores when ((n+k)!)² divides (2n)!.
-/

/--
The central binomial coefficient: C(2n, n) = (2n)! / (n!)²
-/
def centralBinom (n : ℕ) : ℕ := Nat.choose (2 * n) n

/--
Basic identity: (2n)! = C(2n,n) * (n!)²
-/
axiom factorial_2n_eq (n : ℕ) :
    (2 * n)! = centralBinom n * (n !) ^ 2

/-!
## The Main Question

For fixed k ≥ 2, we ask whether there are infinitely many n such that
((n+k)!)² divides (2n)!.

This is equivalent to asking about the ratio (2n)! / ((n+k)!)².
-/

/--
The predicate: ((n+k)!)² divides (2n)!
-/
def divides_factorial (k n : ℕ) : Prop :=
  ((n + k)!) ^ 2 ∣ (2 * n)!

/--
The set of n for which ((n+k)!)² | (2n)!
-/
def divisible_set (k : ℕ) : Set ℕ :=
  { n : ℕ | divides_factorial k n }

/-!
## The Erdős Conjecture (Open for k ≥ 2)

The main conjecture: For every k ≥ 2, the set of n with ((n+k)!)² | (2n)!
is infinite.
-/

/--
**Erdős Problem #727 (Main Conjecture)**: For every k ≥ 2, there are
infinitely many n such that ((n+k)!)² | (2n)!.

**Status**: OPEN
-/
def erdos_727_conjecture : Prop :=
  ∀ k ≥ 2, (divisible_set k).Infinite

/--
The k = 2 case is specifically still open.
-/
def erdos_727_k2_open : Prop :=
  (divisible_set 2).Infinite

/-!
## Balakran's Theorem (k = 1 Case, SOLVED)

In 1929, Balakran proved that for k = 1, there are infinitely many n
such that ((n+1)!)² | (2n)!.

This is equivalent to showing (n+1)² | C(2n, n) for infinitely many n.
-/

/--
**Balakran's Theorem (1929)**: There are infinitely many n such that
((n+1)!)² | (2n)!.

Equivalently: (n+1)² | C(2n, n) for infinitely many n.
-/
axiom balakran_theorem : (divisible_set 1).Infinite

/--
The k = 1 case of Erdős #727 is solved by Balakran.
-/
theorem erdos_727_k1_solved : (divisible_set 1).Infinite := balakran_theorem

/-!
## Classical Result: Catalan Numbers

A classical fact is that (n+1) divides C(2n, n) for ALL n.
The Catalan numbers are defined as C_n = C(2n,n) / (n+1).
-/

/--
The n-th Catalan number: C_n = C(2n,n) / (n+1)
-/
def catalanNumber (n : ℕ) : ℕ := centralBinom n / (n + 1)

/--
Classical fact: (n+1) | C(2n, n) for all n.
-/
axiom catalan_divisibility (n : ℕ) : (n + 1) ∣ centralBinom n

/--
Catalan identity: C(2n,n) = (n+1) * C_n
-/
theorem centralBinom_eq_catalan (n : ℕ) :
    centralBinom n = (n + 1) * catalanNumber n := by
  rw [catalanNumber]
  have h := catalan_divisibility n
  rw [mul_comm]
  exact (Nat.div_mul_cancel h).symm

/-!
## The EGRS Variant (SOLVED)

Erdős, Graham, Ruzsa, and Straus showed a weaker but still interesting result:
For any k ≥ 2, there are infinitely many n such that (n+k)!(n+1)! | (2n)!.

This uses Balakran's method but doesn't quite give the squared version.
-/

/--
The EGRS variant predicate: (n+k)!(n+1)! | (2n)!
-/
def egrs_divides (k n : ℕ) : Prop :=
  (n + k)! * (n + 1)! ∣ (2 * n)!

/--
The set of n satisfying the EGRS variant.
-/
def egrs_set (k : ℕ) : Set ℕ :=
  { n : ℕ | egrs_divides k n }

/--
**EGRS Theorem**: For any k ≥ 2, there are infinitely many n such that
(n+k)!(n+1)! | (2n)!.

In fact, this holds whenever k < c log n for some constant c > 0.
-/
axiom egrs_theorem (k : ℕ) (hk : 2 ≤ k) : (egrs_set k).Infinite

/-!
## Relationship Between the Problems

The EGRS variant is weaker than the main conjecture. If ((n+k)!)² | (2n)!,
then certainly (n+k)!(n+1)! | (2n)! since (n+1)! ≤ (n+k)! for k ≥ 0.
-/

/--
The main divisibility implies the EGRS variant.
-/
theorem main_implies_egrs (k n : ℕ) (h : divides_factorial k n) :
    egrs_divides k n := by
  unfold divides_factorial egrs_divides at *
  -- ((n+k)!)² | (2n)! and (n+1)! | (n+k)! implies (n+k)!(n+1)! | (2n)!
  -- This follows from (n+k)! * (n+1)! | ((n+k)!)² when n+1 ≤ n+k
  sorry

/--
If the main conjecture holds, then the EGRS variant holds.
-/
theorem main_conjecture_implies_egrs (k : ℕ) (_hk : 2 ≤ k)
    (h : (divisible_set k).Infinite) : (egrs_set k).Infinite := by
  apply Infinite.mono (s := divisible_set k)
  · intro n hn
    exact main_implies_egrs k n hn
  · exact h

/-!
## Erdős's Related Result

Erdős (1968) proved a bound: if a! b! | n!, then a + b ≤ n + O(log n).

This gives an upper bound on how "large" the factors can be.
-/

/--
**Erdős (1968)**: If a! b! | n!, then a + b ≤ n + O(log n).

We state this qualitatively: for each n, the pairs (a,b) with a!b! | n!
satisfy a + b ≤ n + C log n for some constant C.
-/
axiom erdos_factorial_bound : ∃ C : ℝ, ∀ n a b : ℕ,
    a.factorial * b.factorial ∣ n.factorial →
    (a : ℝ) + b ≤ n + C * Real.log n

/-!
## Numerical Evidence

For the k = 2 case, we need ((n+2)!)² | (2n)!.

Let's check small values:
- n = 2: (4!)² = 576, (4)! = 24. 576 ∤ 24.
- n = 3: (5!)² = 14400, (6)! = 720. 14400 ∤ 720.
- n = 4: (6!)² = 518400, (8)! = 40320. 518400 ∤ 40320.

For larger n, the ratio (2n)! / ((n+2)!)² grows, but finding exact divisibility
requires careful analysis of prime factorizations.
-/

/--
For small n, we can verify divisibility computationally.
Example: 4! = 24, (2*2)! = 24, so (3!)² = 36 ∤ 24.
-/
example : ¬ divides_factorial 1 2 := by
  unfold divides_factorial
  -- (3!)² = 36, (4)! = 24, and 36 ∤ 24
  decide

/-!
## Why This Problem is Interesting

The problem connects several areas:
1. **Factorial arithmetic**: Understanding divisibility of factorials
2. **Catalan numbers**: The k=1 case relates to Catalan number properties
3. **Prime factorization**: Legendre's formula for prime powers in n!
4. **Analytic number theory**: The Erdős bound uses logarithmic estimates

The gap between k=1 (solved) and k=2 (open) suggests subtle number-theoretic
phenomena at play.
-/

/--
The main problem asks about the squared factor ((n+k)!)².
Understanding why the square makes k ≥ 2 so much harder than k = 1
is an interesting open question.
-/
def square_difficulty : Prop :=
  (divisible_set 1).Infinite ∧  -- k=1 solved
  ¬∃ proof : Prop, proof = (divisible_set 2).Infinite  -- k=2 has no known proof

/-!
## Summary of Status

| Problem | Status | Reference |
|---------|--------|-----------|
| ((n+1)!)² ∣ (2n)! for ∞ many n | SOLVED | Balakran 1929 |
| ((n+k)!)² ∣ (2n)! for k≥2, ∞ many n | OPEN | EGRS 1975 |
| ((n+2)!)² ∣ (2n)! for ∞ many n | OPEN | - |
| (n+k)!(n+1)! ∣ (2n)! for k≥2, ∞ many n | SOLVED | EGRS 1975 |
-/

/--
Summary: The k = 1 case is solved, k ≥ 2 is open.
-/
theorem erdos_727_status :
    (divisible_set 1).Infinite ∧
    (∀ k ≥ 2, (egrs_set k).Infinite) := by
  constructor
  · exact balakran_theorem
  · intro k hk
    exact egrs_theorem k hk

end Erdos727
