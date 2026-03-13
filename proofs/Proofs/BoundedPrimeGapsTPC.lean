/-
# Bounded Prime Gaps - TPC Index-Value Bridge

Completes the full logical equivalence between the Twin Prime Conjecture
(stated in terms of prime *indices*) and the existence of infinitely many
twin prime *pairs* (stated in terms of prime *values*).

## The Gap

BoundedPrimeGaps.lean notes under "What's NOT Proven":
  "Full equivalence of TwinPrimeConjecture and DicksonConjecture {0,2}
   (index vs. value quantification)"

The issue: TwinPrimeConjecture quantifies over indices n with primeGap n = 2,
while DicksonConjecture / twin prime pairs quantify over values p with
p and p+2 both prime. Converting between these requires showing that
twin primes are *consecutive* primes (the index-value bridge).

## What This File Proves

1. `nthPrime_surjective` — every prime is nthPrime k for some k
2. `no_prime_strictly_between_twin` — if p ≥ 3 and p+2 are both prime,
   no prime lies strictly between them (p+1 is even)
3. `twin_primes_are_consecutive` — twin primes p, p+2 with p ≥ 3
   correspond to consecutive entries in the prime sequence
4. `prime_pairs_implies_tpc` — the missing direction:
   (∀ N, ∃ n ≥ N, Prime n ∧ Prime(n+2)) → TwinPrimeConjecture
5. `tpc_iff_twin_prime_pairs` — the full equivalence:
   TPC ↔ infinitely many twin prime pairs

## Mathematical Insight

For p ≥ 3 prime: p is odd, so p+1 is even and ≥ 4, hence composite.
Since the only integer strictly between p and p+2 is p+1, there is no
prime between consecutive twin primes. Therefore nthPrime(k+1) = p+2
whenever nthPrime k = p and p+2 is prime.

Status: DEEP DIVE
Axioms: 0 (all proved from Mathlib + BoundedPrimeGaps infrastructure)
Sorries: 0

Tags: number-theory, prime-gaps, twin-primes, formalization
-/

import Mathlib
import Proofs.BoundedPrimeGaps

namespace BoundedPrimeGapsTPC

open BoundedPrimeGaps Nat Finset

/-
## Part I: Surjectivity of nthPrime

Every prime number appears in the nthPrime enumeration.
This uses Nat.nth_count: if p satisfies the predicate, then
nth(count(p)) = p.
-/

/-- Every prime number is nthPrime k for some k.
    Proof: Nat.nth_count gives nth(count(p)) = p for any p satisfying the predicate. -/
theorem nthPrime_surjective (p : ℕ) (hp : Nat.Prime p) :
    ∃ k, nthPrime k = p := by
  exact ⟨Nat.count Nat.Prime p, Nat.nth_count hp⟩

/-- The index of a prime p is Nat.count Prime p. -/
theorem nthPrime_at_count (p : ℕ) (hp : Nat.Prime p) :
    nthPrime (Nat.count Nat.Prime p) = p :=
  Nat.nth_count hp

/-- If nthPrime k = p and p ≥ 3, then k ≥ 1. -/
lemma index_ge_one_of_prime_ge_three {k p : ℕ} (hk : nthPrime k = p) (hp3 : p ≥ 3) :
    k ≥ 1 := by
  by_contra h
  push_neg at h
  -- k = 0
  have hk0 : k = 0 := by omega
  rw [hk0, nthPrime_zero] at hk
  -- p = 2, contradicting p ≥ 3
  omega

/-
## Part II: No Prime Between Twin Primes

If p ≥ 3 is prime, then p+1 is even (≥ 4), hence composite.
Since the only integer strictly between p and p+2 is p+1,
no prime lies strictly between p and p+2.
-/

/-- If p ≥ 3 is prime, then p+1 is NOT prime (it's even and ≥ 4). -/
lemma succ_of_odd_prime_not_prime (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) :
    ¬ Nat.Prime (p + 1) := by
  intro h_prime
  -- p is odd (prime ≥ 3)
  have hp_odd : ¬ 2 ∣ p := by
    intro h2
    have := hp.eq_one_or_self_of_dvd 2 h2
    rcases this with h | h <;> omega
  -- p+1 is even
  have h_even : 2 ∣ (p + 1) := by omega
  -- p+1 ≥ 4
  have h_ge4 : p + 1 ≥ 4 := by omega
  -- A prime divisible by 2 must be 2, but p+1 ≥ 4
  have := h_prime.eq_one_or_self_of_dvd 2 h_even
  rcases this with h | h <;> omega

/-- No prime lies strictly between p and p+2 when p ≥ 3 is prime.
    The only candidate is p+1, which is even (≥ 4) and thus composite. -/
theorem no_prime_strictly_between_twin (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) :
    ∀ q, p < q → q < p + 2 → ¬ Nat.Prime q := by
  intro q hpq hq2
  -- q = p + 1 (only integer strictly between p and p+2)
  have hq_eq : q = p + 1 := by omega
  rw [hq_eq]
  exact succ_of_odd_prime_not_prime p hp hp3

/-
## Part III: Twin Primes are Consecutive

If nthPrime k = p ≥ 3 and p+2 is prime, then nthPrime(k+1) = p+2.
This means (p, p+2) corresponds to the consecutive prime pair (p_k, p_{k+1}).
-/

/-- If nthPrime k = p with p ≥ 3 and p+2 is prime, then nthPrime(k+1) = p+2.
    Proof strategy:
    - nth_prime_succ_le_of_prime_gt gives nthPrime(k+1) ≤ p+2
    - nthPrime(k+1) > nthPrime k = p, so nthPrime(k+1) ≥ p+1
    - nthPrime(k+1) is prime, and p+1 is not prime (even, ≥ 4)
    - Therefore nthPrime(k+1) = p+2 -/
theorem twin_primes_are_consecutive (k p : ℕ) (hk : nthPrime k = p)
    (hp : Nat.Prime p) (hp3 : p ≥ 3) (hp2 : Nat.Prime (p + 2)) :
    nthPrime (k + 1) = p + 2 := by
  -- Upper bound: nthPrime(k+1) ≤ p+2
  have h_upper : nthPrime (k + 1) ≤ p + 2 := by
    have hlt : nthPrime k < p + 2 := by rw [hk]; omega
    exact PrimeGapBounds.nth_prime_succ_le_of_prime_gt k (p + 2) hp2 hlt
  -- Lower bound: nthPrime(k+1) > p
  have h_lower : nthPrime (k + 1) > p := by
    rw [← hk]
    exact nthPrime_strictMono (Nat.lt_succ_self k)
  -- nthPrime(k+1) ∈ {p+1, p+2}
  have h_range : nthPrime (k + 1) = p + 1 ∨ nthPrime (k + 1) = p + 2 := by omega
  rcases h_range with h | h
  · -- Case nthPrime(k+1) = p+1: impossible, p+1 is not prime
    exfalso
    have h_prime_succ := nthPrime_prime (k + 1)
    rw [h] at h_prime_succ
    exact succ_of_odd_prime_not_prime p hp hp3 h_prime_succ
  · exact h

/-- Corollary: if p ≥ 3, p prime, p+2 prime, then primeGap at the index of p is 2. -/
theorem primeGap_eq_two_of_twin (k p : ℕ) (hk : nthPrime k = p)
    (hp : Nat.Prime p) (hp3 : p ≥ 3) (hp2 : Nat.Prime (p + 2)) :
    primeGap k = 2 := by
  unfold primeGap
  rw [twin_primes_are_consecutive k p hk hp hp3 hp2, hk]
  omega

/-
## Part IV: The Missing Direction

(∀ N, ∃ n ≥ N, Nat.Prime n ∧ Nat.Prime (n + 2)) → TwinPrimeConjecture

Given a twin prime pair (p, p+2) with p sufficiently large, we:
1. Find the index k with nthPrime k = p
2. Show k ≥ N (using nthPrime k = p ≥ nthPrime N and strict monotonicity)
3. Show primeGap k = 2 (by the consecutive twin primes theorem)
-/

/-- If nthPrime k ≥ nthPrime N, then k ≥ N. -/
lemma index_le_of_nthPrime_le {k N : ℕ} (h : nthPrime N ≤ nthPrime k) : N ≤ k := by
  by_contra hlt
  push_neg at hlt
  -- k < N, so nthPrime k < nthPrime N by strict monotonicity
  have := nthPrime_strictMono hlt
  omega

/-- **The missing direction**: infinitely many twin prime pairs implies TPC. -/
theorem prime_pairs_implies_tpc
    (h : ∀ N : ℕ, ∃ n ≥ N, Nat.Prime n ∧ Nat.Prime (n + 2)) :
    TwinPrimeConjecture := by
  intro N
  -- Get a twin prime pair (p, p+2) with p ≥ nthPrime N (≥ N + 2 ≥ 3)
  obtain ⟨p, hp_ge, hp, hp2⟩ := h (nthPrime N)
  -- p ≥ 3: if p = 2 then p+2 = 4 is not prime, contradicting hp2
  have hp3 : p ≥ 3 := by
    by_contra h
    push_neg at h
    have hp2_val : p = 2 := by have := hp.two_le; omega
    rw [hp2_val] at hp2
    exact absurd hp2 (by decide)
  -- Find the index k with nthPrime k = p
  obtain ⟨k, hk⟩ := nthPrime_surjective p hp
  -- k ≥ N
  have hkN : k ≥ N := index_le_of_nthPrime_le (by rw [hk]; exact hp_ge)
  -- k ≥ 1
  have hk1 : k ≥ 1 := index_ge_one_of_prime_ge_three hk hp3
  -- primeGap k = 2
  have hgap := primeGap_eq_two_of_twin k p hk hp hp3 hp2
  exact ⟨k, hkN, hk1, hgap⟩

/-
## Part V: The Full Equivalence

TwinPrimeConjecture ↔ (∀ N, ∃ n ≥ N, Nat.Prime n ∧ Nat.Prime (n + 2))
-/

/-- **Full equivalence**: The Twin Prime Conjecture (index-based) is equivalent to
    the existence of infinitely many twin prime pairs (value-based).

    This completes the gap noted in BoundedPrimeGaps.lean's summary. -/
theorem tpc_iff_twin_prime_pairs :
    TwinPrimeConjecture ↔
    (∀ N : ℕ, ∃ n ≥ N, Nat.Prime n ∧ Nat.Prime (n + 2)) :=
  ⟨twin_primes_implies_pairs, prime_pairs_implies_tpc⟩

/-- **Corollary**: TwinPrimeConjecture ↔ DicksonConjecture {0, 2}

    Combining the existing results:
    - TPC → Dickson: twin_primes_implies_dickson (in BoundedPrimeGaps)
    - Dickson → pairs: hl_a_twin_gives_infinitely_many_pairs (in BoundedPrimeGaps)
    - pairs → TPC: prime_pairs_implies_tpc (proved above)

    This resolves the noted gap. -/
theorem tpc_iff_dickson :
    TwinPrimeConjecture ↔ DicksonConjecture {0, 2} := by
  constructor
  · exact twin_primes_implies_dickson
  · intro hD
    apply prime_pairs_implies_tpc
    exact fun N => by
      have hpairs := dickson_twin_implies_twin_primes hD
      exact hpairs N

/-
## Part VI: Consequences

With the full equivalence established, we can freely convert between
index-based and value-based formulations of twin primes.
-/

/-- TPC implies Polignac(1) via the value-based formulation. -/
theorem tpc_iff_polignac_one :
    TwinPrimeConjecture ↔ PolignacConjecture 1 :=
  ⟨twin_primes_implies_polignac_one, polignac_one_implies_twin_primes⟩

/-- The "bounded prime gaps landscape" - key implications that are now fully formal:
    Dickson {0,2} ↔ TPC ↔ Polignac(1) ↔ infinitely many twin prime pairs -/
theorem prime_gap_equivalence_chain :
    (DicksonConjecture {0, 2} ↔ TwinPrimeConjecture) ∧
    (TwinPrimeConjecture ↔ PolignacConjecture 1) ∧
    (TwinPrimeConjecture ↔ (∀ N : ℕ, ∃ n ≥ N, Nat.Prime n ∧ Nat.Prime (n + 2))) :=
  ⟨tpc_iff_dickson.symm, tpc_iff_polignac_one, tpc_iff_twin_prime_pairs⟩

/-
## Summary

This file proves 10 new results, all without sorries or axioms:

1. `nthPrime_surjective` — inverse of nthPrime: every prime has an index
2. `nthPrime_at_count` — explicit formula via Nat.count
3. `index_ge_one_of_prime_ge_three` — primes ≥ 3 have index ≥ 1
4. `succ_of_odd_prime_not_prime` — p+1 composite for odd prime p
5. `no_prime_strictly_between_twin` — no prime between p and p+2
6. `twin_primes_are_consecutive` — twin primes are consecutive in enumeration
7. `primeGap_eq_two_of_twin` — primeGap = 2 at twin prime indices
8. `prime_pairs_implies_tpc` — the missing direction of the TPC equivalence
9. `tpc_iff_twin_prime_pairs` — full TPC ↔ pairs equivalence
10. `tpc_iff_dickson` — full TPC ↔ Dickson {0,2} equivalence
11. `prime_gap_equivalence_chain` — Dickson ↔ TPC ↔ Polignac(1) ↔ pairs

Mathematical significance: Completes the formal connection between the
"index-based" (primeGap n = 2) and "value-based" (Prime p ∧ Prime(p+2))
formulations of the Twin Prime Conjecture. Resolves the gap noted in
BoundedPrimeGaps.lean's summary section.

Axioms: 0
Sorries: 0
-/

end BoundedPrimeGapsTPC
