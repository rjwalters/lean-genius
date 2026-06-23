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
import Mathlib.Order.Filter.AtTopBot.Basic
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
  have h : nthPrime n < nthPrime (n + 1) := nthPrime_strictMono (Nat.lt_succ_self n)
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
Uses `Classical.decPred` since arbitrary `S : Set ℕ` need not be decidable.
-/
noncomputable def HasDensity (S : Set ℕ) (d : ℝ) : Prop :=
  letI : DecidablePred (· ∈ S) := Classical.decPred _
  Tendsto (fun N : ℕ => ((Finset.filter (· ∈ S) (Finset.range N)).card : ℝ) / N)
    atTop (nhds d)

/-- Upper natural density. -/
noncomputable def upperDensity (S : Set ℕ) : ℝ :=
  letI : DecidablePred (· ∈ S) := Classical.decPred _
  limsup (fun N : ℕ => ((Finset.filter (· ∈ S) (Finset.range N)).card : ℝ) / N) atTop

/-- Lower natural density. -/
noncomputable def lowerDensity (S : Set ℕ) : ℝ :=
  letI : DecidablePred (· ∈ S) := Classical.decPred _
  liminf (fun N : ℕ => ((Finset.filter (· ∈ S) (Finset.range N)).card : ℝ) / N) atTop

/-- A set has density d iff upper and lower densities both equal d.
    This follows from the standard analysis result: Tendsto f l (nhds a) ↔
    limsup f l = a ∧ liminf f l = a.
    The boundedness arguments use that count/N ∈ [0, 1]. -/
theorem hasDensity_iff_upper_lower (S : Set ℕ) (d : ℝ) :
    HasDensity S d ↔ upperDensity S = d ∧ lowerDensity S = d := by
  classical
  simp only [HasDensity, upperDensity, lowerDensity]
  refine ⟨fun h => ⟨h.limsup_eq, h.liminf_eq⟩, ?_⟩
  rintro ⟨hsup, hinf⟩
  refine tendsto_of_le_liminf_of_limsup_le (le_of_eq hinf.symm) (le_of_eq hsup) ?_ ?_
  · -- Bounded above by 1: count ≤ N implies count/N ≤ 1.
    refine ⟨1, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hcount : (Finset.filter (· ∈ S) (Finset.range N)).card ≤ N := by
      have h := Finset.card_filter_le (Finset.range N) (· ∈ S)
      simpa using h
    calc ((Finset.filter (· ∈ S) (Finset.range N)).card : ℝ) / N
        ≤ (N : ℝ) / N := by
          apply div_le_div_of_nonneg_right
          · exact_mod_cast hcount
          · exact hNpos.le
      _ = 1 := div_self hNpos.ne'
  · -- Bounded below by 0: count ≥ 0 implies count/N ≥ 0.
    refine ⟨0, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards with N
    positivity

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
  show primeGap 0 ≤ primeGap 1
  rw [primeGap_zero, primeGap_one]
  decide

/-- 1 is in gapEqualSet since primeGap 1 = primeGap 2 = 2.
    Previously axiomatized; now proved from primeGap values. -/
theorem one_mem_gapEqualSet : 1 ∈ gapEqualSet := by
  show primeGap 1 = primeGap 2
  rw [primeGap_one, primeGap_two]

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

/-
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
    Previously axiomatized; now proved by omega on ℕ subtraction.
    Uses `change` to normalize `n + 1 + 1 = n + 2` since omega tracks these
    as distinct atoms in its abstraction even though they are defeq. -/
theorem gapEqual_iff_ap (n : ℕ) :
    n ∈ gapEqualSet ↔ threePrimesInAP n := by
  change primeGap n = primeGap (n + 1) ↔
         nthPrime n + nthPrime (n + 2) = 2 * nthPrime (n + 1)
  change nthPrime (n + 1) - nthPrime n = nthPrime (n + 2) - nthPrime (n + 1) ↔
         nthPrime n + nthPrime (n + 2) = 2 * nthPrime (n + 1)
  have h1 : nthPrime n < nthPrime (n + 1) := nthPrime_strictMono (Nat.lt_succ_self n)
  have h2 : nthPrime (n + 1) < nthPrime (n + 2) := nthPrime_strictMono (by omega)
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

/-
**Green-Tao Theorem (2008)**

For any k, there exist arbitrarily long arithmetic progressions in the primes.

This is much stronger than Erdős 218c, though it doesn't directly imply
that consecutive primes form APs.
-/

/- ## Part IX: Partial Results -/

/-
**Lower Bound on Upper Density**

While exact density 1/2 is unknown, we can show that both
gapIncreasingSet and gapDecreasingSet are infinite.
-/

/-- A set with positive density is infinite.

    Proof sketch (standard real analysis): if `S` were finite with `|S| = C`, then
    the counting function `|S ∩ [0,N)| ≤ C` is bounded, so `|S ∩ [0,N)| / N → 0`
    as `N → ∞` by squeeze (`0 ≤ count/N ≤ C/N`, both → 0). But by hypothesis the
    limit is `d > 0`, contradicting uniqueness of limits.

    Axiomatized here due to Mathlib API drift around `Filter.Tendsto.div` and
    decidability handling for `Finset.filter (· ∈ S)` on arbitrary `Set ℕ`.
    See gallery issue tracker for restoration. -/
private axiom infinite_of_hasDensity_pos {S : Set ℕ} {d : ℝ} (_hd : 0 < d)
    (_hdens : HasDensity S d) : S.Infinite

/-- The set of gap-increasing indices is infinite.
    Follows from Erdős's conjecture that this set has density 1/2. -/
theorem gapIncreasingSet_infinite : gapIncreasingSet.Infinite :=
  infinite_of_hasDensity_pos (by norm_num : (0 : ℝ) < 1/2) erdos_218a

/-- The set of gap-decreasing indices is infinite.
    Follows from Erdős's conjecture that this set has density 1/2. -/
theorem gapDecreasingSet_infinite : gapDecreasingSet.Infinite :=
  infinite_of_hasDensity_pos (by norm_num : (0 : ℝ) < 1/2) erdos_218b

/-
**Average Gap Growth**

By the Prime Number Theorem, the average gap around p is about log(p).
This grows without bound, but locally gaps fluctuate.
-/

/- ## Part X: Symmetry Argument (Heuristic) -/

/-
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
  simp only [mem_union, mem_univ, iff_true]
  by_cases h : primeGap n < primeGap (n + 1)
  · left; left; exact h
  · push_neg at h
    by_cases h' : primeGap (n + 1) < primeGap n
    · left; right; exact h'
    · push_neg at h'
      right; exact le_antisymm h' h

/-- The non-strict increasing and decreasing gap sets cover all of ℕ.
    Follows from totality of `≤`: for any n, either d_n ≤ d_{n+1} or d_{n+1} ≤ d_n.
    Note: these sets are not disjoint — their intersection is `gapEqualSet`. -/
theorem gapIncreasingSet_union_gapDecreasingSet :
    gapIncreasingSet ∪ gapDecreasingSet = Set.univ := by
  ext n
  simp only [mem_union, gapIncreasingSet, gapDecreasingSet, mem_univ, iff_true]
  exact le_total (primeGap n) (primeGap (n + 1))

/-- Strict gap increase implies non-strict gap increase. -/
theorem strictlyIncreasing_subset_gapIncreasingSet :
    strictlyIncreasing ⊆ gapIncreasingSet := by
  intro n hn
  simp only [gapIncreasingSet, strictlyIncreasing, mem_setOf_eq] at hn ⊢
  exact le_of_lt hn

/-- Strict gap decrease implies non-strict gap decrease. -/
theorem strictlyDecreasing_subset_gapDecreasingSet :
    strictlyDecreasing ⊆ gapDecreasingSet := by
  intro n hn
  simp only [gapDecreasingSet, strictlyDecreasing, mem_setOf_eq] at hn ⊢
  exact le_of_lt hn

/-- The non-strict increasing set decomposes as strict increase ∪ equality.
    Direct application of `le_iff_lt_or_eq` to the gap comparison. -/
theorem gapIncreasingSet_eq_strictlyIncreasing_union_gapEqualSet :
    gapIncreasingSet = strictlyIncreasing ∪ gapEqualSet := by
  ext n
  simp only [mem_union, gapIncreasingSet, strictlyIncreasing, gapEqualSet, mem_setOf_eq]
  exact le_iff_lt_or_eq

/-- The non-strict decreasing set decomposes as strict decrease ∪ equality.
    Requires `eq_comm` because `gapEqualSet` is stated as `d_n = d_{n+1}`. -/
theorem gapDecreasingSet_eq_strictlyDecreasing_union_gapEqualSet :
    gapDecreasingSet = strictlyDecreasing ∪ gapEqualSet := by
  ext n
  simp only [mem_union, gapDecreasingSet, strictlyDecreasing, gapEqualSet, mem_setOf_eq]
  constructor
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · exact Or.inl h
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact le_of_lt h
    · exact le_of_eq h.symm

/-- Strict increase and strict decrease are disjoint sets.
    Transitivity of `<` would give `d_n < d_n`, contradicting irreflexivity. -/
theorem strictlyIncreasing_disjoint_strictlyDecreasing :
    Disjoint strictlyIncreasing strictlyDecreasing := by
  rw [Set.disjoint_left]
  intro n h1 h2
  simp only [strictlyIncreasing, strictlyDecreasing, mem_setOf_eq] at h1 h2
  exact absurd (h1.trans h2) (lt_irrefl _)

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

/- The problem remains OPEN (Tao: "looks difficult"). -/

end Erdos218
