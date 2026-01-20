/-
Erdős Problem #886: Divisors Near the Square Root (Ruzsa's Conjecture)

Source: https://erdosproblems.com/886
Status: OPEN

Statement:
Let ε > 0. Is it true that, for all large n, the number of divisors of n
in the interval (√n, √n + n^{1/2-ε}) is O_ε(1)?

In other words: can the divisors of n "cluster" near √n, or are they
necessarily spread out?

Attribution:
Erdős attributes this conjecture to Imre Z. Ruzsa.

Related Results:
- Erdős and Rosenfeld (1997) proved there are infinitely many n with
  four divisors in (√n, √n + n^{1/4})

See also Problem #887.

Tags: Number theory, Divisors, Distribution of divisors
-/

import Mathlib.Data.Nat.Divisors
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Floor

open Nat Finset Real

namespace Erdos886

/-
## Part I: Divisors of n
-/

/--
**Divisors of n:**
The set of positive divisors of n.
-/
def divisorsOf (n : ℕ) : Finset ℕ := n.divisors

/--
**Divisor Count:**
The number of divisors of n, denoted τ(n) or d(n).
-/
def divisorCount (n : ℕ) : ℕ := (divisorsOf n).card

/--
Every positive integer has at least one divisor (itself).
-/
theorem divisorCount_pos (n : ℕ) (hn : n ≥ 1) : divisorCount n ≥ 1 := by
  sorry

/-
## Part II: The Interval Near √n
-/

/--
**The Critical Interval:**
The interval (√n, √n + n^{1/2-ε}) for small ε > 0.
This is where Ruzsa conjectures divisors cannot cluster.
-/
noncomputable def criticalInterval (n : ℕ) (ε : ℝ) : Set ℝ :=
  {x : ℝ | Real.sqrt n < x ∧ x < Real.sqrt n + (n : ℝ)^(1/2 - ε)}

/--
**Width of the Critical Interval:**
The interval has width n^{1/2-ε}, which shrinks relative to √n as n grows.
-/
noncomputable def intervalWidth (n : ℕ) (ε : ℝ) : ℝ :=
  (n : ℝ)^(1/2 - ε)

/--
For large n, the interval width is o(√n).
-/
axiom intervalWidth_sublinear (ε : ℝ) (hε : ε > 0) :
    ∀ C : ℝ, C > 0 → ∃ N : ℕ, ∀ n ≥ N,
      intervalWidth n ε < C * Real.sqrt n

/-
## Part III: Divisors in the Critical Interval
-/

/--
**Divisors in Interval:**
The set of divisors of n lying in the interval (a, b).
-/
def divisorsInInterval (n : ℕ) (a b : ℝ) : Finset ℕ :=
  (divisorsOf n).filter (fun d => a < (d : ℝ) ∧ (d : ℝ) < b)

/--
**Count of Divisors Near √n:**
The number of divisors of n in the critical interval.
-/
noncomputable def divisorsNearSqrt (n : ℕ) (ε : ℝ) : ℕ :=
  (divisorsInInterval n (Real.sqrt n) (Real.sqrt n + intervalWidth n ε)).card

/-
## Part IV: Ruzsa's Conjecture
-/

/--
**Ruzsa's Conjecture (Erdős Problem #886):**
For all ε > 0, there exists C_ε such that for all large n,
the number of divisors of n in (√n, √n + n^{1/2-ε}) is at most C_ε.

In symbols: divisorsNearSqrt(n, ε) = O_ε(1)
-/
def ruzsaConjecture : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ C : ℕ, C > 0 ∧
      ∃ N : ℕ, ∀ n ≥ N,
        divisorsNearSqrt n ε ≤ C

/--
**Erdős Problem #886: OPEN**
The conjecture remains unresolved.
-/
theorem erdos_886_open : True := trivial

/-
## Part V: Erdős-Rosenfeld Result
-/

/--
**Erdős-Rosenfeld Theorem (1997):**
There are infinitely many n with four divisors in (√n, √n + n^{1/4}).

Note: This uses ε = 1/4, which gives a wider interval than the conjecture.
It shows that divisors CAN cluster to some extent, but doesn't resolve
whether the bounded count holds for arbitrarily small ε.
-/
axiom erdos_rosenfeld_four_divisors :
    ∃ S : Set ℕ, S.Infinite ∧
      ∀ n ∈ S, divisorsNearSqrt n (1/4 : ℝ) ≥ 4

/--
The Erdős-Rosenfeld result for the specific interval (√n, √n + n^{1/4}).
-/
axiom erdos_rosenfeld :
    ∀ k : ℕ, k ≥ 1 → ∃ n : ℕ, n ≥ k ∧
      (divisorsInInterval n (Real.sqrt n) (Real.sqrt n + (n : ℝ)^(1/4 : ℝ))).card ≥ 4

/-
## Part VI: The Factor-Difference Set
-/

/--
**Factor-Difference Set:**
Given n, the set {d - d' : d, d' | n, d > d'} of differences between divisors.
This is related to how divisors are distributed.
-/
def factorDifferenceSet (n : ℕ) : Finset ℤ :=
  (divisorsOf n).product (divisorsOf n)
    |>.filter (fun dd' => dd'.1 > dd'.2)
    |>.image (fun dd' => (dd'.1 : ℤ) - (dd'.2 : ℤ))

/--
The factor-difference set captures spacing between divisors.
-/
theorem factorDifferenceSet_nonempty (n : ℕ) (hn : (divisorsOf n).card ≥ 2) :
    (factorDifferenceSet n).Nonempty := by
  sorry

/-
## Part VII: Divisor Density Near √n
-/

/--
**Local Divisor Density:**
The "density" of divisors near √n, measured by count / interval width.
-/
noncomputable def localDivisorDensity (n : ℕ) (ε : ℝ) : ℝ :=
  (divisorsNearSqrt n ε : ℝ) / intervalWidth n ε

/--
**Ruzsa's Conjecture Reformulated:**
The local divisor density near √n goes to 0 as n → ∞.
-/
def ruzsaConjectureAlt : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∀ δ : ℝ, δ > 0 → ∃ N : ℕ, ∀ n ≥ N,
      localDivisorDensity n ε < δ

/--
The two formulations are equivalent.
-/
axiom conjecture_equivalence :
    ruzsaConjecture ↔ ruzsaConjectureAlt

/-
## Part VIII: Examples
-/

/--
**Highly Composite Numbers:**
Numbers with many divisors (like n = 2^k or n = k!) have divisors more
spread out, not clustered near √n.
-/
def isHighlyComposite (n : ℕ) : Prop :=
  ∀ m : ℕ, m < n → divisorCount m < divisorCount n

/--
**Squares:**
For n = m², the divisor √n = m is exactly a divisor.
The interval (m, m + m^{1-2ε}) contains d if m < d < m + m^{1-2ε}.
-/
theorem square_example (m : ℕ) (hm : m ≥ 2) :
    m ∣ (m * m) ∧ (m * m : ℝ).sqrt = m := by
  constructor
  · exact Nat.dvd_mul_right m m
  · sorry

/-
## Part IX: Connection to Problem #887
-/

/--
**Problem #887 Connection:**
Problem 887 asks a related question about divisor distribution.
The two problems are closely linked in the study of how divisors
are distributed relative to √n.
-/
axiom related_to_887 : True  -- Connection stated in problem description

/-
## Part X: Bounds and Partial Results
-/

/--
**Trivial Upper Bound:**
The number of divisors in ANY interval of length L is at most τ(n).
-/
theorem trivial_bound (n : ℕ) (ε : ℝ) (hε : ε > 0) (hn : n ≥ 1) :
    divisorsNearSqrt n ε ≤ divisorCount n := by
  unfold divisorsNearSqrt divisorCount divisorsInInterval
  apply card_filter_le

/--
**Divisor Count Bound:**
τ(n) ≤ 2√n for all n ≥ 1.
-/
axiom divisor_count_bound (n : ℕ) (hn : n ≥ 1) :
    (divisorCount n : ℝ) ≤ 2 * Real.sqrt n

/-
## Part XI: Summary
-/

/--
**Erdős Problem #886: Summary**

An open problem about divisor clustering near √n.

**The Question:** For any ε > 0, is the count of divisors of n in
(√n, √n + n^{1/2-ε}) bounded by a constant depending only on ε?

**Status:** OPEN

**Known Results:**
- Erdős-Rosenfeld (1997): Infinitely many n have 4 divisors in (√n, √n + n^{1/4})
- The conjecture is attributed to Imre Z. Ruzsa
- Related to Problem #887
-/
theorem erdos_886_summary :
    -- The problem is open
    True ∧
    -- The trivial bound holds
    (∀ n ε, ε > 0 → n ≥ 1 → divisorsNearSqrt n ε ≤ divisorCount n) :=
  ⟨trivial, fun n ε _ hn => trivial_bound n ε ‹ε > 0› hn⟩

end Erdos886
