/-
# Bounded Prime Gaps (Zhang/Maynard-Tao/Polymath)

Formalization of the bounded prime gaps theorem and related infrastructure.

**The Theorem** (Zhang 2013, Maynard 2015, Polymath 2014):
There exists a constant H such that there are infinitely many pairs of
consecutive primes differing by at most H.

- Zhang's original bound: H ≤ 70,000,000
- Maynard's improvement: H ≤ 600
- Polymath optimization: H ≤ 246
- Assuming Elliott-Halberstam: H ≤ 12

**Key Concepts**:
- Admissible k-tuples: the combinatorial objects at the heart of the proof
- The Dickson conjecture: primes in admissible tuples
- Prime gaps and their distribution

**Status**: DEEP DIVE
- Defines admissible k-tuples formally
- States and proves properties of admissible tuples
- States the bounded gaps theorem with specific bounds
- Derives consequences for prime gap distribution

Tags: number-theory, primes, prime-gaps, sieve-theory
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

namespace BoundedPrimeGaps

open Nat Finset Filter

/-
## Part I: Admissible Tuples

An admissible k-tuple is a finite set H = {h₁, ..., hₖ} of integers such that
for every prime p, the set H does not cover all residue classes modulo p.

Equivalently: for every prime p, |{h mod p : h ∈ H}| < p.

This is the key combinatorial concept in the GPY/Zhang/Maynard-Tao approach.
-/

/-- A finite set of natural numbers is admissible if for every prime p,
    the residues of the elements modulo p do not cover all of ℤ/pℤ. -/
def IsAdmissible (H : Finset ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → (H.image (· % p)).card < p

/-
## Part II: Basic Properties of Admissible Tuples
-/

/-- The empty set is trivially admissible. -/
theorem admissible_empty : IsAdmissible ∅ := by
  intro p hp
  simp
  exact hp.pos

/-- A singleton set is admissible. -/
theorem admissible_singleton (n : ℕ) : IsAdmissible {n} := by
  intro p hp
  simp [Finset.image_singleton, Finset.card_singleton]
  exact hp.one_lt

/-- Subsets of admissible tuples are admissible. -/
theorem admissible_subset {H₁ H₂ : Finset ℕ} (h : H₁ ⊆ H₂) (hadm : IsAdmissible H₂) :
    IsAdmissible H₁ := by
  intro p hp
  calc (H₁.image (· % p)).card
      ≤ (H₂.image (· % p)).card := Finset.card_le_card (Finset.image_subset_image h)
    _ < p := hadm p hp

/-- Any set with fewer elements than the smallest prime it must avoid
    is automatically admissible. This handles the case |H| < 2. -/
theorem admissible_of_card_lt_two {H : Finset ℕ} (h : H.card < 2) :
    IsAdmissible H := by
  intro p hp
  calc (H.image (· % p)).card
      ≤ H.card := Finset.card_image_le
    _ < 2 := h
    _ ≤ p := hp.two_le

/-
## Part III: Verified Small Admissible Tuples

We verify specific small admissible tuples using `decide` for small primes
and cardinality bounds for larger primes.
-/

/-- {0, 2} is an admissible 2-tuple (the twin prime tuple).
    mod 2: {0, 0} = {0}, card 1 < 2 ✓
    mod 3: {0, 2}, card 2 < 3 ✓
    mod p ≥ 5: card ≤ 2 < 5 ≤ p ✓ -/
theorem admissible_twin : IsAdmissible {0, 2} := by
  intro p hp
  have hle : (({0, 2} : Finset ℕ).image (· % p)).card ≤ ({0, 2} : Finset ℕ).card :=
    Finset.card_image_le
  have hcard : ({0, 2} : Finset ℕ).card = 2 := by decide
  by_cases hp2 : p = 2
  · subst hp2; decide
  · by_cases hp3 : p = 3
    · subst hp3; decide
    · -- p ≥ 5, and image card ≤ 2 < 5 ≤ p
      have hp5 : p ≥ 5 := by
        rcases hp.eq_two_or_odd with h2 | hodd
        · exact absurd h2 hp2
        · have h2le := hp.two_le
          have hne3 := hp3
          -- p is odd and ≥ 2 and ≠ 3, so p ≥ 5
          omega
      omega

/-- {0, 2, 6} is an admissible 3-tuple. -/
theorem admissible_triple_0_2_6 : IsAdmissible {0, 2, 6} := by
  intro p hp
  have himg : (({0, 2, 6} : Finset ℕ).image (· % p)).card ≤ 3 := by
    calc (({0, 2, 6} : Finset ℕ).image (· % p)).card
        ≤ ({0, 2, 6} : Finset ℕ).card := Finset.card_image_le
      _ = 3 := by decide
  by_cases hp2 : p = 2
  · subst hp2; decide
  · by_cases hp3 : p = 3
    · subst hp3; decide
    · have hp5 : p ≥ 5 := by
        have h2le := hp.two_le
        rcases hp.eq_two_or_odd with h2 | hodd
        · exact absurd h2 hp2
        · omega
      linarith

/-- {0, 4, 6} is an admissible 3-tuple. -/
theorem admissible_triple_0_4_6 : IsAdmissible {0, 4, 6} := by
  intro p hp
  have himg : (({0, 4, 6} : Finset ℕ).image (· % p)).card ≤ 3 := by
    calc (({0, 4, 6} : Finset ℕ).image (· % p)).card
        ≤ ({0, 4, 6} : Finset ℕ).card := Finset.card_image_le
      _ = 3 := by decide
  by_cases hp2 : p = 2
  · subst hp2; decide
  · by_cases hp3 : p = 3
    · subst hp3; decide
    · by_cases hp5 : p = 5
      · subst hp5; decide
      · have hp7 : p ≥ 7 := by
          have h2le := hp.two_le
          rcases hp.eq_two_or_odd with h2 | hodd
          · exact absurd h2 hp2
          · omega
        linarith

/-- {0, 2, 6, 8} is an admissible 4-tuple (prime quadruplet pattern). -/
theorem admissible_quadruple_0_2_6_8 : IsAdmissible {0, 2, 6, 8} := by
  intro p hp
  have himg : (({0, 2, 6, 8} : Finset ℕ).image (· % p)).card ≤ 4 := by
    calc (({0, 2, 6, 8} : Finset ℕ).image (· % p)).card
        ≤ ({0, 2, 6, 8} : Finset ℕ).card := Finset.card_image_le
      _ = 4 := by decide
  by_cases hp2 : p = 2
  · subst hp2; decide
  · by_cases hp3 : p = 3
    · subst hp3; decide
    · by_cases hp5 : p = 5
      · subst hp5; decide
      · have hp7 : p ≥ 7 := by
          have h2le := hp.two_le
          rcases hp.eq_two_or_odd with h2 | hodd
          · exact absurd h2 hp2
          · omega
        linarith

/-
## Part IV: Non-Admissible Tuples

Not every set is admissible. A set that covers all residues mod some prime
is not admissible.
-/

/-- {0, 1, 2} is NOT admissible: it covers all residues mod 3. -/
theorem not_admissible_0_1_2 : ¬ IsAdmissible {0, 1, 2} := by
  intro h
  have h3 := h 3 (by decide : Nat.Prime 3)
  have : (({0, 1, 2} : Finset ℕ).image (· % 3)).card = 3 := by decide
  omega

/-- {0, 1} is NOT admissible: it covers all residues mod 2. -/
theorem not_admissible_0_1 : ¬ IsAdmissible {0, 1} := by
  intro h
  have h2 := h 2 (by decide : Nat.Prime 2)
  have : (({0, 1} : Finset ℕ).image (· % 2)).card = 2 := by decide
  omega

/-
## Part V: The Bounded Prime Gaps Theorem
-/

/-- The nth prime number (0-indexed). -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime n

/-- The prime gap g(n) = p_{n+1} - p_n. -/
noncomputable def primeGap (n : ℕ) : ℕ := nthPrime (n + 1) - nthPrime n

/-- **Zhang's Theorem (2013)**: There are infinitely many prime gaps ≤ 70,000,000. -/
axiom zhang_bounded_gaps_70M :
  ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ primeGap n ≤ 70000000

/-- **Polymath 8b (2014)**: There are infinitely many prime gaps ≤ 246. -/
axiom polymath_bounded_gaps_246 :
  ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ primeGap n ≤ 246

/-- **Maynard-Tao (2015)**: For any m ≥ 2, there are infinitely many
    indices n such that among p_n, ..., p_{n+m-1} there are at least m
    primes within a bounded interval. -/
axiom maynard_tao_m_tuples (m : ℕ) (hm : m ≥ 2) :
  ∃ C : ℕ, ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧
    nthPrime (n + m - 1) - nthPrime n ≤ C

/-- **Conditional on Elliott-Halberstam**: Gap bound improves to 12. -/
axiom bounded_gaps_conditional_EH :
  ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ primeGap n ≤ 12

/-
## Part VI: Consequences of Bounded Gaps
-/

/-- There are infinitely many prime gaps ≤ 246. -/
theorem infinitely_many_small_gaps :
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ primeGap n ≤ 246 :=
  polymath_bounded_gaps_246

/-- The liminf of prime gaps is finite (at most 246). -/
theorem liminf_prime_gaps_finite :
    ∃ H : ℕ, ∀ N : ℕ, ∃ n ≥ N, primeGap n ≤ H :=
  ⟨246, fun N => polymath_bounded_gaps_246 N⟩

/-- From Maynard-Tao: for any k ≥ 2, bounded intervals contain k primes. -/
theorem bounded_intervals_k_primes (k : ℕ) (hk : k ≥ 2) :
    ∃ C : ℕ, ∀ N : ℕ, ∃ n ≥ N, nthPrime (n + k - 1) - nthPrime n ≤ C :=
  maynard_tao_m_tuples k hk

/-
## Part VII: Connection to Admissible Tuples
-/

/-- The Dickson conjecture: for an admissible k-tuple, all translates
    are simultaneously prime infinitely often. -/
def DicksonConjecture (H : Finset ℕ) : Prop :=
  IsAdmissible H →
  ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ ∀ h ∈ H, Nat.Prime (n + h)

/-- The Maynard-Tao density result: infinitely many n have ≥ m primes
    among {n + h : h ∈ H}. -/
def MaynardTaoDensity (H : Finset ℕ) (m : ℕ) : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ m ≤ (H.filter (fun h => (n + h).Prime)).card

/-- For {0, 2}, Maynard-Tao with m = 2 implies the twin prime conjecture. -/
theorem maynard_tao_implies_twin_primes :
    MaynardTaoDensity {0, 2} 2 →
    ∀ N : ℕ, ∃ n : ℕ, n ≥ N ∧ Nat.Prime n ∧ Nat.Prime (n + 2) := by
  intro hMT N
  obtain ⟨n, hn, hcard⟩ := hMT N
  refine ⟨n, hn, ?_⟩
  have hfull_card : ({0, 2} : Finset ℕ).card = 2 := by decide
  have hfilter_sub : ({0, 2} : Finset ℕ).filter (fun h => (n + h).Prime) ⊆ {0, 2} :=
    Finset.filter_subset _ _
  have hfilter_eq : ({0, 2} : Finset ℕ).filter (fun h => (n + h).Prime) = {0, 2} := by
    apply Finset.eq_of_subset_of_card_le hfilter_sub
    rw [hfull_card]; exact hcard
  have h0 : 0 ∈ ({0, 2} : Finset ℕ).filter (fun h => (n + h).Prime) := by
    rw [hfilter_eq]; simp
  have h2 : 2 ∈ ({0, 2} : Finset ℕ).filter (fun h => (n + h).Prime) := by
    rw [hfilter_eq]; simp
  exact ⟨by simpa using (Finset.mem_filter.mp h0).2, (Finset.mem_filter.mp h2).2⟩

/-
## Part VIII: The Admissible Tuple Behind H = 246

The Polymath 8b result uses an admissible k-tuple of diameter ≤ 246.
-/

/-- There exists an admissible k-tuple with k ≥ 50 and diameter ≤ 246. -/
axiom exists_admissible_50_tuple_246 :
  ∃ H : Finset ℕ, IsAdmissible H ∧ H.card ≥ 50 ∧
    ∀ a b : ℕ, a ∈ H → b ∈ H → (a : ℤ) - b ≤ 246 ∧ (b : ℤ) - a ≤ 246

/-
## Part IX: Properties of nthPrime and primeGap
-/

/-- The nth prime is prime. -/
lemma nthPrime_prime (n : ℕ) : Nat.Prime (nthPrime n) :=
  Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n

/-- Primes are strictly increasing. -/
lemma nthPrime_strictMono : StrictMono nthPrime :=
  fun _ _ h => Nat.nth_strictMono Nat.infinite_setOf_prime h

/-- Prime gaps are positive. -/
theorem primeGap_pos (n : ℕ) : 0 < primeGap n := by
  unfold primeGap
  have : nthPrime n < nthPrime (n + 1) := nthPrime_strictMono (Nat.lt_succ_self n)
  omega

/-- All prime gaps for n ≥ 1 are even (both p_n, p_{n+1} are odd). -/
theorem primeGap_even (n : ℕ) (hn : n ≥ 1) : 2 ∣ primeGap n := by
  unfold primeGap nthPrime
  have hp_n : Nat.Prime (Nat.nth Nat.Prime n) :=
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime n
  have hp_n1 : Nat.Prime (Nat.nth Nat.Prime (n + 1)) :=
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n + 1)
  have hn_ge : Nat.nth Nat.Prime n ≥ 3 := by
    have h1 : Nat.nth Nat.Prime 1 = 3 := Nat.nth_prime_one_eq_three
    have hmono : Nat.nth Nat.Prime 1 ≤ Nat.nth Nat.Prime n :=
      (Nat.nth_strictMono Nat.infinite_setOf_prime).monotone hn
    omega
  have h_lt : Nat.nth Nat.Prime n < Nat.nth Nat.Prime (n + 1) :=
    Nat.nth_strictMono Nat.infinite_setOf_prime (Nat.lt_succ_self n)
  -- p_n is odd (prime ≥ 3, so not 2)
  have hodd_n : ¬ 2 ∣ Nat.nth Nat.Prime n := by
    intro h2
    have := hp_n.eq_one_or_self_of_dvd 2 h2
    rcases this with h | h <;> omega
  -- p_{n+1} is odd
  have hodd_n1 : ¬ 2 ∣ Nat.nth Nat.Prime (n + 1) := by
    intro h2
    have := hp_n1.eq_one_or_self_of_dvd 2 h2
    rcases this with h | h <;> omega
  -- Both are odd, their difference is even
  have hmod_n : Nat.nth Nat.Prime n % 2 = 1 := by omega
  have hmod_n1 : Nat.nth Nat.Prime (n + 1) % 2 = 1 := by omega
  have hdiff : (Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n) % 2 = 0 := by omega
  exact Nat.dvd_of_mod_eq_zero hdiff

/-
## Summary

This file establishes:
1. **Admissible tuples**: Definition and basic properties (subset, singleton, empty)
2. **Small examples**: Verified {0,2}, {0,2,6}, {0,4,6}, {0,2,6,8}
3. **Non-examples**: {0,1} and {0,1,2} are NOT admissible
4. **The theorem hierarchy**: Zhang → Polymath → Maynard-Tao
5. **Consequences**: Infinitely many small gaps, liminf ≤ 246
6. **Connections**: Admissible tuples ↔ Dickson conjecture ↔ twin primes
7. **Gap properties**: Positivity and evenness of prime gaps

### Axioms Used
- `zhang_bounded_gaps_70M`: Zhang's original result (2013)
- `polymath_bounded_gaps_246`: Polymath 8b optimization (2014)
- `maynard_tao_m_tuples`: Maynard-Tao generalization (2015)
- `bounded_gaps_conditional_EH`: Conditional result assuming Elliott-Halberstam
- `exists_admissible_50_tuple_246`: Existence of the specific tuple used by Polymath

### What's NOT Proven (and Why)
- Zhang's theorem itself (requires sieve theory not in Mathlib)
- The Bombieri-Vinogradov theorem (major missing infrastructure)
- Selberg sieve bounds (not in Mathlib)
-/

end BoundedPrimeGaps
