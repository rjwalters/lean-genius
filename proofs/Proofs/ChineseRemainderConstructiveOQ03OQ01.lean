/-
  Chinese Remainder Theorem — OQ-03-OQ-01:
  Optimality of prime RNS bases for ALL k (not just k ≤ 6)

  The parent file `ChineseRemainderConstructiveOQ03` formalizes efficient
  Residue Number System (RNS) bases. There the "primorial" — the product of
  the first k primes, which is the dynamic range of the k-channel prime base —
  is a *lookup table* defined only for k ≤ 6:

      def primorial : ℕ → ℕ
        | 0 => 1 | 1 => 2 | 2 => 6 | 3 => 30 | 4 => 210 | 5 => 2310 | 6 => 30030
        | _ => 0

  and the growth bound `primorial k ≥ 2^k` is proved by `interval_cases`,
  valid only for 1 ≤ k ≤ 6. The parent docstring states the bound holds for all
  k "but proving it generally requires a proper definition of the k-th prime."

  This file supplies exactly that proper definition, using Mathlib's `Nat.nth`
  (the n-th element of an infinite set), and proves the optimality-relevant
  facts for ALL k:

  * `kthPrime i = Nat.nth Nat.Prime i` — the i-th prime (0-indexed), defined
    for every i, with `kthPrime` prime, ≥ 2, strictly monotone, injective.
  * `primorialProper k = ∏ first k primes` — defined for every k.
  * `primorialProper_ge_two_pow : 2^k ≤ primorialProper k` for ALL k.
  * `primorialProper_strictMono` — the dynamic range strictly increases in k.
  * The first-k-primes list is pairwise coprime and bounded below by 2 for
    every k, hence yields a genuine `RNSBase` with k channels and dynamic
    range ≥ 2^k for ALL k (`firstPrimeBase`).
  * Cross-check: the proper primorial reproduces the classical primorial values
    `1, 2, 6, 30, 210, 2310, 30030` for k = 0..6.

  This does NOT settle the deeper open question of *full* optimality of prime
  bases (that consecutive primes maximize the dynamic range subject to a width
  budget under all coprimality decompositions) — that remains open. What is
  delivered is the all-k generalization of the growth lower bound, the missing
  piece the parent explicitly deferred.

  NOTE: the parent file `ChineseRemainderConstructiveOQ03.lean` no longer
  compiles against the current Mathlib (4.26.0) — it has bit-rotted. So this
  file is deliberately SELF-CONTAINED: it re-declares a minimal `RNSBase`
  structure rather than importing the parent, and cross-checks the primorial
  values against the classical sequence directly.

  Status: VERIFIED
  Axioms: 0
  Sorries: 0

  References:
  [Gar59] Garner "The residue number system" (1959)
  [SS67] Szabó-Tanaka "Residue Arithmetic and Its Applications" (1967)

  Tags: number-theory, modular-arithmetic, algorithms, prime-counting, classical
-/

import Mathlib

namespace RNSBasesAllK

open Nat

-- ============================================================
-- SECTION 0: Minimal RNS base (self-contained re-declaration)
-- ============================================================

/-- An RNS base: a list of pairwise coprime moduli, all ≥ 2.
    (Mirrors the parent's `RNSBases.RNSBase`, re-declared here because the
    parent file no longer compiles against the current Mathlib.) -/
structure RNSBase where
  moduli : List ℕ
  coprime : moduli.Pairwise Nat.Coprime
  ge_two : ∀ m ∈ moduli, m ≥ 2

/-- Number of channels (moduli). -/
def RNSBase.channels (b : RNSBase) : ℕ := b.moduli.length

/-- Dynamic range: product of all moduli. -/
def RNSBase.dynamicRange (b : RNSBase) : ℕ := b.moduli.prod

-- ============================================================
-- SECTION I: A proper k-th prime, defined for all k
-- ============================================================

/-- The `i`-th prime (0-indexed): `kthPrime 0 = 2`, `kthPrime 1 = 3`, ….
    Uses Mathlib's `Nat.nth`, the enumerator of the infinite set of primes,
    so it is total: defined for every `i : ℕ`. -/
noncomputable def kthPrime (i : ℕ) : ℕ := Nat.nth Nat.Prime i

/-- Every `kthPrime i` is prime. -/
theorem kthPrime_prime (i : ℕ) : (kthPrime i).Prime := Nat.prime_nth_prime i

/-- Every `kthPrime i` is at least 2. -/
theorem kthPrime_two_le (i : ℕ) : 2 ≤ kthPrime i := (kthPrime_prime i).two_le

/-- Every `kthPrime i` is positive. -/
theorem kthPrime_pos (i : ℕ) : 0 < kthPrime i := (kthPrime_prime i).pos

/-- The prime enumerator is strictly monotone (primes are infinite). -/
theorem kthPrime_strictMono : StrictMono kthPrime :=
  Nat.nth_strictMono Nat.infinite_setOf_prime

/-- Distinct indices give distinct primes. -/
theorem kthPrime_injective : Function.Injective kthPrime :=
  kthPrime_strictMono.injective

/-- Characterization: the `(count Prime n)`-th prime is `n`, for prime `n`. -/
theorem kthPrime_count {n : ℕ} (hn : n.Prime) :
    kthPrime (Nat.count Nat.Prime n) = n :=
  Nat.nth_count hn

theorem kthPrime_zero : kthPrime 0 = 2 := by
  have hc : Nat.count Nat.Prime 2 = 0 := by decide
  have h := kthPrime_count (n := 2) (by norm_num)
  rwa [hc] at h

theorem kthPrime_one : kthPrime 1 = 3 := by
  have hc : Nat.count Nat.Prime 3 = 1 := by decide
  have h := kthPrime_count (n := 3) (by norm_num)
  rwa [hc] at h

theorem kthPrime_two : kthPrime 2 = 5 := by
  have hc : Nat.count Nat.Prime 5 = 2 := by decide
  have h := kthPrime_count (n := 5) (by norm_num)
  rwa [hc] at h

theorem kthPrime_three : kthPrime 3 = 7 := by
  have hc : Nat.count Nat.Prime 7 = 3 := by decide
  have h := kthPrime_count (n := 7) (by norm_num)
  rwa [hc] at h

theorem kthPrime_four : kthPrime 4 = 11 := by
  have hc : Nat.count Nat.Prime 11 = 4 := by decide
  have h := kthPrime_count (n := 11) (by norm_num)
  rwa [hc] at h

theorem kthPrime_five : kthPrime 5 = 13 := by
  have hc : Nat.count Nat.Prime 13 = 5 := by decide
  have h := kthPrime_count (n := 13) (by norm_num)
  rwa [hc] at h

-- ============================================================
-- SECTION II: The proper primorial, defined for all k
-- ============================================================

/-- The first `k` primes, as a list: `[kthPrime 0, …, kthPrime (k-1)]`. -/
noncomputable def firstPrimes (k : ℕ) : List ℕ := (List.range k).map kthPrime

/-- The proper primorial: the product of the first `k` primes.
    Unlike the parent's lookup table, this is defined for EVERY `k`. -/
noncomputable def primorialProper (k : ℕ) : ℕ := (firstPrimes k).prod

theorem firstPrimes_succ (k : ℕ) :
    firstPrimes (k + 1) = firstPrimes k ++ [kthPrime k] := by
  unfold firstPrimes
  rw [List.range_succ, List.map_append]
  rfl

theorem primorialProper_zero : primorialProper 0 = 1 := by
  unfold primorialProper firstPrimes; simp

/-- The defining recurrence: each step multiplies by the next prime. -/
theorem primorialProper_succ (k : ℕ) :
    primorialProper (k + 1) = primorialProper k * kthPrime k := by
  unfold primorialProper
  rw [firstPrimes_succ, List.prod_append]
  simp

/-- The proper primorial is always positive. -/
theorem primorialProper_pos : ∀ k, 0 < primorialProper k
  | 0 => by simp [primorialProper, firstPrimes]
  | (k + 1) => by
      rw [primorialProper_succ]
      exact Nat.mul_pos (primorialProper_pos k) (kthPrime_pos k)

/-- **Main result.** The growth lower bound `2^k ≤ primorialProper k` holds for
    ALL `k`, generalizing the parent's `interval_cases` proof for k ≤ 6.
    Each of the `k` prime factors is at least 2, so the product dominates `2^k`. -/
theorem primorialProper_ge_two_pow : ∀ k, 2 ^ k ≤ primorialProper k
  | 0 => by simp [primorialProper, firstPrimes]
  | (k + 1) => by
      rw [pow_succ, primorialProper_succ]
      exact Nat.mul_le_mul (primorialProper_ge_two_pow k) (kthPrime_two_le k)

/-- The dynamic range of the k-channel prime base strictly increases with `k`. -/
theorem primorialProper_strictMono : StrictMono primorialProper := by
  apply strictMono_nat_of_lt_succ
  intro k
  rw [primorialProper_succ]
  have h1 := primorialProper_pos k
  have h2 := kthPrime_two_le k
  calc primorialProper k < primorialProper k * 2 := by omega
    _ ≤ primorialProper k * kthPrime k := Nat.mul_le_mul (le_refl _) h2

/-- Consequence: the dynamic range is unbounded — for every target `M` there is
    a number of channels `k` whose prime base exceeds it. -/
theorem primorialProper_unbounded (M : ℕ) : ∃ k, M < primorialProper k :=
  ⟨M + 1, lt_of_lt_of_le (by have := Nat.lt_two_pow_self (n := M + 1); omega)
    (primorialProper_ge_two_pow (M + 1))⟩

-- ============================================================
-- SECTION III: Cross-check against the parent lookup table
-- ============================================================

/-- Cross-check: the proper primorial reproduces the classical primorial
    sequence `1, 2, 6, 30, 210, 2310, 30030` for `k = 0, …, 6`. This confirms
    the all-`k` definition specializes correctly to the parent's lookup table. -/
theorem primorialProper_values :
    primorialProper 0 = 1 ∧ primorialProper 1 = 2 ∧ primorialProper 2 = 6 ∧
    primorialProper 3 = 30 ∧ primorialProper 4 = 210 ∧
    primorialProper 5 = 2310 ∧ primorialProper 6 = 30030 := by
  refine ⟨primorialProper_zero, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [primorialProper_succ, primorialProper_zero,
      kthPrime_zero, kthPrime_one, kthPrime_two, kthPrime_three,
      kthPrime_four, kthPrime_five]

-- ============================================================
-- SECTION IV: The prime RNS base, valid for all k
-- ============================================================

/-- Every modulus in `firstPrimes k` is at least 2. -/
theorem firstPrimes_ge_two {k m : ℕ} (hm : m ∈ firstPrimes k) : 2 ≤ m := by
  unfold firstPrimes at hm
  rw [List.mem_map] at hm
  obtain ⟨i, _, rfl⟩ := hm
  exact kthPrime_two_le i

/-- The first `k` primes are pairwise coprime — for EVERY `k`.
    (Parent only checked specific small lists like `[2,3,5]`, `[2,3,5,7,11,13]`.) -/
theorem firstPrimes_pairwise_coprime (k : ℕ) :
    (firstPrimes k).Pairwise Nat.Coprime := by
  unfold firstPrimes
  refine (List.pairwise_lt_range (n := k)).map kthPrime (fun a b hab => ?_)
  exact (Nat.coprime_primes (kthPrime_prime a) (kthPrime_prime b)).mpr
    (fun h => (Nat.ne_of_lt hab) (kthPrime_injective h))

/-- The genuine RNS base on the first `k` primes — valid for every `k`. -/
noncomputable def firstPrimeBase (k : ℕ) : RNSBase where
  moduli := firstPrimes k
  coprime := firstPrimes_pairwise_coprime k
  ge_two := fun _ hm => firstPrimes_ge_two hm

/-- The prime base has exactly `k` channels. -/
theorem firstPrimeBase_channels (k : ℕ) : (firstPrimeBase k).channels = k := by
  unfold RNSBase.channels firstPrimeBase firstPrimes
  simp

/-- Its dynamic range is the proper primorial. -/
theorem firstPrimeBase_dynamicRange (k : ℕ) :
    (firstPrimeBase k).dynamicRange = primorialProper k := rfl

/-- **Optimality bound for all k.** For every number of channels `k`, the
    first-`k`-primes RNS base achieves dynamic range at least `2^k`. This is the
    all-`k` generalization of the parent's `primorial_growth_lower` (k ≤ 6). -/
theorem firstPrimeBase_dynamicRange_ge_two_pow (k : ℕ) :
    2 ^ k ≤ (firstPrimeBase k).dynamicRange := by
  rw [firstPrimeBase_dynamicRange]
  exact primorialProper_ge_two_pow k

-- ============================================================
-- SECTION V: Summary
-- ============================================================

/-- Capstone: for every `k`, there is a valid RNS base with exactly `k`
    channels whose dynamic range is at least `2^k`. The k-th prime is given by
    a total, proper definition (`Nat.nth Nat.Prime`), settling the all-`k`
    growth bound the parent file deferred. -/
theorem prime_base_growth_all_k (k : ℕ) :
    (firstPrimeBase k).channels = k ∧ 2 ^ k ≤ (firstPrimeBase k).dynamicRange :=
  ⟨firstPrimeBase_channels k, firstPrimeBase_dynamicRange_ge_two_pow k⟩

#check @prime_base_growth_all_k
#check @primorialProper_ge_two_pow
#check @primorialProper_values

end RNSBasesAllK
