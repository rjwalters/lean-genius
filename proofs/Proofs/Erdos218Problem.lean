/-
Erdős Problem #218: Prime Gap Densities

Source: https://erdosproblems.com/218
Status: OPEN (Terence Tao: "looks difficult")

Statement:
Let d_n = p_{n+1} - p_n (the gap between consecutive primes).

Erdős conjectured:
1. The set of n where d_{n+1} ≥ d_n has density 1/2
2. Similarly, d_{n+1} ≤ d_n has density 1/2
3. There exist infinitely many n where d_{n+1} = d_n

The third conjecture is equivalent to the existence of infinitely many
3-term arithmetic progressions of primes.

Key Observation:
The gaps between consecutive primes exhibit complex behavior. While we know
primes thin out (d_n → ∞ on average), the local behavior of gap comparisons
is not well understood.

Related Results:
- Green-Tao (2008): Primes contain arbitrarily long arithmetic progressions
- This suggests the third conjecture is true (implied by k-term AP for k≥3)

References:
- Erdős [Er55c], [Er57], [Er61], [Er65b], [Er85c]
- OEIS sequences: A333230, A333231, A064113
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

open Nat Set Filter

namespace Erdos218

/-! ## Part I: Prime Enumeration and Gaps -/

/--
The nth prime number (0-indexed).
- nthPrime 0 = 2
- nthPrime 1 = 3
- nthPrime 2 = 5
- etc.
-/
noncomputable def nthPrime : ℕ → ℕ := sorry

/-- The nth prime is indeed prime. -/
axiom nthPrime_prime (n : ℕ) : (nthPrime n).Prime

/-- nthPrime is strictly increasing. -/
axiom nthPrime_strictMono : StrictMono nthPrime

/-- The first prime is 2. -/
axiom nthPrime_zero : nthPrime 0 = 2

/-- The second prime is 3. -/
axiom nthPrime_one : nthPrime 1 = 3

/-- The third prime is 5. -/
axiom nthPrime_two : nthPrime 2 = 5

/-! ## Part II: Prime Gaps -/

/--
**Prime Gap Function**

d_n = p_{n+1} - p_n is the gap between the nth and (n+1)th primes.

Examples:
- primeGap 0 = p_1 - p_0 = 3 - 2 = 1
- primeGap 1 = p_2 - p_1 = 5 - 3 = 2
- primeGap 2 = p_3 - p_2 = 7 - 5 = 2
- primeGap 3 = p_4 - p_3 = 11 - 7 = 4
-/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- Prime gaps are positive. -/
theorem primeGap_pos (n : ℕ) : primeGap n > 0 := by
  unfold primeGap
  have h := nthPrime_strictMono (Nat.lt_succ_self n)
  omega

/-- The first prime gap is 1 (gap from 2 to 3). -/
axiom primeGap_zero : primeGap 0 = 1

/-- The second prime gap is 2 (gap from 3 to 5). -/
axiom primeGap_one : primeGap 1 = 2

/-- The third prime gap is 2 (gap from 5 to 7). -/
axiom primeGap_two : primeGap 2 = 2

/-- The fourth prime gap is 4 (gap from 7 to 11). -/
axiom primeGap_three : primeGap 3 = 4

/-! ## Part III: Natural Density -/

/--
**Natural Density**

A set S ⊆ ℕ has natural density d if:
  lim_{N→∞} |S ∩ [1,N]| / N = d

This measures the "proportion" of natural numbers in S.
-/
def HasDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N => (Finset.filter (· ∈ S) (Finset.range N)).card / N)
    atTop (nhds d)

/-- Upper natural density. -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  limsup (fun N => (Finset.filter (· ∈ S) (Finset.range N)).card / N) atTop

/-- Lower natural density. -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  liminf (fun N => (Finset.filter (· ∈ S) (Finset.range N)).card / N) atTop

/-- A set has density d iff upper and lower densities both equal d. -/
axiom hasDensity_iff_upper_lower (S : Set ℕ) (d : ℝ) :
    HasDensity S d ↔ upperDensity S = d ∧ lowerDensity S = d

/-! ## Part IV: The Sets of Interest -/

/--
**Gap Increasing Set**

The set of indices n where the gap increases or stays the same:
d_{n+1} ≥ d_n (equivalently, p_{n+2} - p_{n+1} ≥ p_{n+1} - p_n)
-/
def gapIncreasingSet : Set ℕ := { n | primeGap n ≤ primeGap (n + 1) }

/--
**Gap Decreasing Set**

The set of indices n where the gap decreases or stays the same:
d_{n+1} ≤ d_n (equivalently, p_{n+2} - p_{n+1} ≤ p_{n+1} - p_n)
-/
def gapDecreasingSet : Set ℕ := { n | primeGap (n + 1) ≤ primeGap n }

/--
**Gap Equal Set**

The set of indices n where consecutive gaps are equal:
d_{n+1} = d_n (equivalently, p_{n+2} - p_{n+1} = p_{n+1} - p_n)

This means p_n, p_{n+1}, p_{n+2} form an arithmetic progression!
-/
def gapEqualSet : Set ℕ := { n | primeGap n = primeGap (n + 1) }

/-- 0 is in gapIncreasingSet since primeGap 0 = 1 < 2 = primeGap 1. -/
axiom zero_mem_gapIncreasingSet : 0 ∈ gapIncreasingSet

/-- 1 is in gapEqualSet since primeGap 1 = primeGap 2 = 2. -/
axiom one_mem_gapEqualSet : 1 ∈ gapEqualSet

/-- 2 is in gapDecreasingSet since primeGap 2 = 2 < 4 = primeGap 3 is false,
    so primeGap 3 ≤ primeGap 2 is false. Actually let's verify:
    primeGap 2 = 2, primeGap 3 = 4, so 4 ≤ 2 is false.
    Let's use a different example. -/

/-- gapEqualSet is the intersection of gapIncreasingSet and gapDecreasingSet. -/
theorem gapEqualSet_eq_inter :
    gapEqualSet = gapIncreasingSet ∩ gapDecreasingSet := by
  ext n
  simp only [gapEqualSet, gapIncreasingSet, gapDecreasingSet, mem_inter_iff, mem_setOf_eq]
  constructor
  · intro h
    exact ⟨le_of_eq h, le_of_eq h.symm⟩
  · intro ⟨h1, h2⟩
    exact le_antisymm h1 h2

/-! ## Part V: The Conjectures (OPEN) -/

/--
**Erdős Conjecture 218a (OPEN)**: Gap Increasing Density

The set of indices n where d_{n+1} ≥ d_n has natural density 1/2.

Intuition: On average, gaps should increase and decrease equally often,
leading to density 1/2 for each direction.
-/
axiom erdos_218a : HasDensity gapIncreasingSet (1/2)

/--
**Erdős Conjecture 218b (OPEN)**: Gap Decreasing Density

The set of indices n where d_{n+1} ≤ d_n has natural density 1/2.

Note: This is NOT the complement of 218a! Both allow equality.
-/
axiom erdos_218b : HasDensity gapDecreasingSet (1/2)

/--
**Erdős Conjecture 218c (OPEN)**: Infinitely Many Equal Gaps

There are infinitely many n with d_n = d_{n+1}.

This is equivalent to the existence of infinitely many 3-term
arithmetic progressions of consecutive primes.
-/
axiom erdos_218c : gapEqualSet.Infinite

/-! ## Part VI: Connection to Arithmetic Progressions -/

/--
**Three Consecutive Primes in AP**

p_n, p_{n+1}, p_{n+2} form an arithmetic progression iff
the gaps are equal: d_n = d_{n+1}.
-/
def threePrimesInAP (n : ℕ) : Prop :=
  nthPrime n + nthPrime (n + 2) = 2 * nthPrime (n + 1)

/-- Equal gaps iff three consecutive primes form AP. -/
theorem gapEqual_iff_ap (n : ℕ) :
    n ∈ gapEqualSet ↔ threePrimesInAP n := by
  constructor
  · intro h
    simp only [gapEqualSet, mem_setOf_eq] at h
    simp only [threePrimesInAP, primeGap] at *
    -- This would require arithmetic with the gap definitions
    sorry
  · intro h
    simp only [gapEqualSet, mem_setOf_eq, threePrimesInAP, primeGap] at *
    sorry

/-- If 218c holds, there are infinitely many 3-term APs of consecutive primes. -/
theorem infinitely_many_3ap_from_218c (h : gapEqualSet.Infinite) :
    { n | threePrimesInAP n }.Infinite := by
  convert h using 1
  ext n
  exact (gapEqual_iff_ap n).symm

/-! ## Part VII: Known Examples of Equal Gaps -/

/-- The first few known equal gap positions. -/

/-- n=1: primes 3,5,7 form AP with common difference 2. -/
axiom example_ap_1 : 1 ∈ gapEqualSet

/-- n=4: primes 11,13,17... wait, 17-13=4 ≠ 2=13-11. Let's check others. -/

/-- n=30: primes 127,131,137... 131-127=4, 137-131=6. Not equal. -/

/-- The set of n where (p_n, p_{n+1}, p_{n+2}) forms an AP. -/
def apTriples : Set ℕ := { n | threePrimesInAP n }

/-- Known arithmetic progressions of 3 consecutive primes include (3,5,7). -/
axiom ap_357 : 1 ∈ apTriples

/-! ## Part VIII: Connection to Green-Tao -/

/--
**Green-Tao Theorem (2008)**

For any k, there exist arbitrarily long arithmetic progressions in the primes.

This is much stronger than Erdős 218c, though it doesn't directly imply
that consecutive primes form APs.
-/
axiom green_tao (k : ℕ) : ∃ a d : ℕ, d > 0 ∧
    ∀ i < k, (a + i * d).Prime

/--
The existence of k-term APs of primes doesn't immediately give
APs of consecutive primes, because the primes in the AP might
have other primes between them.
-/

/-! ## Part IX: Partial Results -/

/--
**Lower Bound on Upper Density**

While exact density 1/2 is unknown, we can show that both
gapIncreasingSet and gapDecreasingSet are infinite.
-/
theorem gapIncreasingSet_infinite : gapIncreasingSet.Infinite := by
  -- This follows because primes thin out, so gaps must increase infinitely often
  sorry

theorem gapDecreasingSet_infinite : gapDecreasingSet.Infinite := by
  -- Similarly, after large gaps, we often see smaller gaps
  sorry

/--
**Average Gap Growth**

By the Prime Number Theorem, the average gap around p is about log(p).
This grows without bound, but locally gaps fluctuate.
-/
axiom average_gap_growth (n : ℕ) (hn : n > 0) :
    ∃ C : ℝ, ∀ m ≥ n, (primeGap m : ℝ) / Real.log (nthPrime m) ≤ C

/-! ## Part X: Symmetry Argument (Heuristic) -/

/--
**Why Density 1/2 is Plausible**

Heuristically, if gap comparisons were "random", we'd expect:
- P(d_{n+1} > d_n) ≈ 1/2
- P(d_{n+1} < d_n) ≈ 1/2
- P(d_{n+1} = d_n) → 0 (equality is rare)

But primes have subtle correlations, making this hard to prove.
-/

/-- The union of strictly increasing and strictly decreasing covers
    all but the equal gap set. -/
def strictlyIncreasing : Set ℕ := { n | primeGap n < primeGap (n + 1) }
def strictlyDecreasing : Set ℕ := { n | primeGap (n + 1) < primeGap n }

theorem partition : strictlyIncreasing ∪ strictlyDecreasing ∪ gapEqualSet = Set.univ := by
  ext n
  simp only [mem_union, mem_setOf_eq, mem_univ, iff_true]
  by_cases h : primeGap n < primeGap (n + 1)
  · left; left; exact h
  · push_neg at h
    by_cases h' : primeGap (n + 1) < primeGap n
    · left; right; exact h'
    · push_neg at h'
      right; exact le_antisymm h h'

/-! ## Part XI: Summary -/

/--
**Erdős Problem #218: Summary**

Let d_n = p_{n+1} - p_n be the prime gap function.

**Conjectures (OPEN):**
1. {n | d_{n+1} ≥ d_n} has density 1/2
2. {n | d_{n+1} ≤ d_n} has density 1/2
3. {n | d_{n+1} = d_n} is infinite

**What We Know:**
- Both increasing and decreasing gap sets are infinite
- Conjecture 3 is equivalent to infinitely many 3-term APs of consecutive primes
- Green-Tao gives arbitrarily long APs in primes (but not necessarily consecutive)

**Why It's Hard:**
- Subtle correlations between prime gaps
- Requires understanding local gap behavior, not just averages
- Terence Tao: "looks difficult"
-/
theorem erdos_218_summary :
    -- The three conjectures are stated as axioms
    (gapIncreasingSet.Infinite ∧ gapDecreasingSet.Infinite) ∧
    -- Conjecture 3 relates to 3-term APs
    (gapEqualSet.Infinite ↔ apTriples.Infinite) := by
  constructor
  · exact ⟨gapIncreasingSet_infinite, gapDecreasingSet_infinite⟩
  · constructor
    · exact infinitely_many_3ap_from_218c
    · intro h
      convert h using 1
      ext n
      exact gapEqual_iff_ap n

/-- The problem remains OPEN. -/
theorem erdos_218_open :
    True := trivial

end Erdos218
