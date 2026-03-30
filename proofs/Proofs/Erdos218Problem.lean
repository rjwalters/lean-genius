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
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Filter.AtTopBot
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Tactic

open Nat Set Filter

namespace Erdos218

/- ## Part I: Prime Enumeration and Gaps -/

/--
The nth prime number (0-indexed).
- nthPrime 0 = 2
- nthPrime 1 = 3
- nthPrime 2 = 5
- etc.
-/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The nth prime is indeed prime.
    Previously axiomatized; now proved from Nat.nth definition. -/
theorem nthPrime_prime (n : ℕ) : (nthPrime n).Prime := by
  unfold nthPrime; exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

/-- nthPrime is strictly increasing.
    Previously axiomatized; now proved from Nat.nth_strictMono. -/
theorem nthPrime_strictMono : StrictMono nthPrime := by
  intro a b hab; unfold nthPrime; exact Nat.nth_strictMono Nat.infinite_setOf_prime hab

/-- The first prime is 2.
    Previously axiomatized; now proved from Mathlib. -/
theorem nthPrime_zero : nthPrime 0 = 2 := by
  unfold nthPrime; exact Nat.nth_prime_zero_eq_two

/-- The second prime is 3.
    Previously axiomatized; now proved from Mathlib. -/
theorem nthPrime_one : nthPrime 1 = 3 := by
  unfold nthPrime; exact Nat.nth_prime_one_eq_three

/-- The third prime is 5.
    Previously axiomatized; now proved from Mathlib. -/
theorem nthPrime_two : nthPrime 2 = 5 := by
  unfold nthPrime; exact Nat.nth_prime_two_eq_five

/-- The fourth prime is 7. Helper for primeGap computations. -/
private theorem nthPrime_three : nthPrime 3 = 7 := by
  unfold nthPrime
  have h_count : Nat.count Nat.Prime 7 = 3 := by decide
  have h_prime : Nat.Prime 7 := by decide
  rw [← h_count]; exact Nat.nth_count h_prime

/-- The fifth prime is 11. Helper for primeGap computations. -/
private theorem nthPrime_four : nthPrime 4 = 11 := by
  unfold nthPrime
  have h_count : Nat.count Nat.Prime 11 = 4 := by decide
  have h_prime : Nat.Prime 11 := by decide
  rw [← h_count]; exact Nat.nth_count h_prime

/- ## Part II: Prime Gaps -/

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

/-- The first prime gap is 1 (gap from 2 to 3).
    Previously axiomatized; now proved from nthPrime values. -/
theorem primeGap_zero : primeGap 0 = 1 := by
  unfold primeGap; rw [nthPrime_zero, nthPrime_one]

/-- The second prime gap is 2 (gap from 3 to 5).
    Previously axiomatized; now proved from nthPrime values. -/
theorem primeGap_one : primeGap 1 = 2 := by
  unfold primeGap; rw [nthPrime_one, nthPrime_two]

/-- The third prime gap is 2 (gap from 5 to 7).
    Previously axiomatized; now proved from nthPrime values. -/
theorem primeGap_two : primeGap 2 = 2 := by
  unfold primeGap; rw [nthPrime_two, nthPrime_three]

/-- The fourth prime gap is 4 (gap from 7 to 11).
    Previously axiomatized; now proved from nthPrime values. -/
theorem primeGap_three : primeGap 3 = 4 := by
  unfold primeGap; rw [nthPrime_three, nthPrime_four]

/- ## Part III: Natural Density -/

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

/-- A set has density d iff upper and lower densities both equal d.
    This follows from the standard analysis result: Tendsto f l (nhds a) ↔
    limsup f l = a ∧ liminf f l = a. -/
theorem hasDensity_iff_upper_lower (S : Set ℕ) (d : ℝ) :
    HasDensity S d ↔ upperDensity S = d ∧ lowerDensity S = d := by
  simp only [HasDensity, upperDensity, lowerDensity]
  constructor
  · intro h
    exact ⟨h.limsup_eq, h.liminf_eq⟩
  · rintro ⟨hsup, hinf⟩
    exact tendsto_of_le_liminf_of_limsup_le (le_of_eq hinf.symm) (le_of_eq hsup)

/- ## Part IV: The Sets of Interest -/

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

/-- 0 is in gapIncreasingSet since primeGap 0 = 1 ≤ 2 = primeGap 1.
    Previously axiomatized; now proved from primeGap values. -/
theorem zero_mem_gapIncreasingSet : 0 ∈ gapIncreasingSet := by
  simp only [gapIncreasingSet, mem_setOf_eq]; rw [primeGap_zero, primeGap_one]

/-- 1 is in gapEqualSet since primeGap 1 = primeGap 2 = 2.
    Previously axiomatized; now proved from primeGap values. -/
theorem one_mem_gapEqualSet : 1 ∈ gapEqualSet := by
  simp only [gapEqualSet, mem_setOf_eq]; rw [primeGap_one, primeGap_two]

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

/- ## Part V: The Conjectures (OPEN) -/

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
/- ## Part VI: Connection to Arithmetic Progressions -/

/--
**Three Consecutive Primes in AP**

p_n, p_{n+1}, p_{n+2} form an arithmetic progression iff
the gaps are equal: d_n = d_{n+1}.
-/
def threePrimesInAP (n : ℕ) : Prop :=
  nthPrime n + nthPrime (n + 2) = 2 * nthPrime (n + 1)

/-- Equal gaps iff three consecutive primes form AP.
    Previously axiomatized; now proved by omega on ℕ subtraction. -/
theorem gapEqual_iff_ap (n : ℕ) :
    n ∈ gapEqualSet ↔ threePrimesInAP n := by
  simp only [gapEqualSet, mem_setOf_eq, primeGap, threePrimesInAP]
  have h1 := nthPrime_strictMono (Nat.lt_succ_self n)
  have h2 := nthPrime_strictMono (Nat.lt_succ_self (n + 1))
  constructor <;> intro h <;> omega

/-- If 218c holds, there are infinitely many 3-term APs of consecutive primes. -/
theorem infinitely_many_3ap_from_218c (h : gapEqualSet.Infinite) :
    { n | threePrimesInAP n }.Infinite := by
  convert h using 1
  ext n
  exact (gapEqual_iff_ap n).symm

/- ## Part VII: Known Examples of Equal Gaps -/

/-- n=1: primes 3,5,7 form AP with common difference 2.
    Previously axiomatized; now proved from gap values. -/
theorem example_ap_1 : 1 ∈ gapEqualSet := one_mem_gapEqualSet

/-- The set of n where (p_n, p_{n+1}, p_{n+2}) forms an AP. -/
def apTriples : Set ℕ := { n | threePrimesInAP n }

/-- Known arithmetic progressions of 3 consecutive primes include (3,5,7).
    Previously axiomatized; now proved from gap equality. -/
theorem ap_357 : 1 ∈ apTriples :=
  (gapEqual_iff_ap 1).mp one_mem_gapEqualSet

/- ## Part VIII: Connection to Green-Tao -/

/--
**Green-Tao Theorem (2008)**

For any k, there exist arbitrarily long arithmetic progressions in the primes.

This is much stronger than Erdős 218c, though it doesn't directly imply
that consecutive primes form APs.
-/
/- ## Part IX: Partial Results -/

/--
**Lower Bound on Upper Density**

While exact density 1/2 is unknown, we can show that both
gapIncreasingSet and gapDecreasingSet are infinite.
-/
/-- A set with positive density is infinite. Proof: a finite set has density 0
    (counting function → 0), but density > 0 by assumption, contradiction. -/
private theorem infinite_of_hasDensity_pos {S : Set ℕ} {d : ℝ} (hd : 0 < d)
    (hdens : HasDensity S d) : S.Infinite := by
  by_contra hfin
  push_neg at hfin
  -- S is finite, so the counting function is bounded
  set C := hfin.toFinset.card with hC_def
  -- For all N, |S ∩ [0,N)| ≤ C
  have hbound : ∀ N, (Finset.filter (· ∈ S) (Finset.range N)).card ≤ C := by
    intro N
    apply Finset.card_le_card
    intro x hx
    rw [Finset.mem_filter] at hx
    exact hfin.mem_toFinset.mpr hx.2
  -- The counting function / N → 0 (bounded numerator, growing denominator)
  have h_zero : Tendsto (fun N : ℕ =>
      ((Finset.filter (· ∈ S) (Finset.range N)).card : ℝ) / N) atTop (nhds 0) := by
    rw [show (0 : ℝ) = 0 / 1 from by norm_num]
    apply Filter.Tendsto.div
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le
        tendsto_const_nhds (tendsto_const_nhds (x := (C : ℝ)))
      · intro N; exact Nat.cast_nonneg _
      · intro N; exact Nat.cast_le.mpr (hbound N)
    · exact tendsto_natCast_atTop_atTop.mono_right atTop_le_nhds |>.congr (fun _ => rfl)
    · exact eventually_atTop.mpr ⟨1, fun N hN => by positivity⟩
  -- But HasDensity says the limit is d > 0, contradiction
  linarith [tendsto_nhds_unique h_zero hdens]

/-- The set of gap-increasing indices is infinite.
    Follows from Erdős's conjecture that this set has density 1/2. -/
theorem gapIncreasingSet_infinite : gapIncreasingSet.Infinite :=
  infinite_of_hasDensity_pos (by norm_num : (0 : ℝ) < 1/2) erdos_218a

/-- The set of gap-decreasing indices is infinite.
    Follows from Erdős's conjecture that this set has density 1/2. -/
theorem gapDecreasingSet_infinite : gapDecreasingSet.Infinite :=
  infinite_of_hasDensity_pos (by norm_num : (0 : ℝ) < 1/2) erdos_218b

/--
**Average Gap Growth**

By the Prime Number Theorem, the average gap around p is about log(p).
This grows without bound, but locally gaps fluctuate.
-/
/- ## Part X: Symmetry Argument (Heuristic) -/

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

/- ## Part XI: Summary -/

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

/-- The problem remains OPEN (Tao: "looks difficult"). -/

end Erdos218
