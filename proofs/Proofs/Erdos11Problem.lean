/-
  Erdős Problem #11: Squarefree + Power of 2

  Source: https://erdosproblems.com/11
  Status: OPEN (verified computationally up to 2^50)

  Statement:
  Is every odd n > 1 the sum of a squarefree number and a power of 2?

  The conjecture has deep connections to Wieferich primes. Granville and
  Soundararajan (1998) proved that if the conjecture holds, then infinitely
  many primes are non-Wieferich (i.e., 2^(p-1) ≢ 1 mod p²).

  Hercher (2024) verified the conjecture for all odd integers up to 2^50.
-/

import Mathlib

open Nat Finset

/-! ## Core Definitions -/

/-- A number is squarefree if no prime square divides it -/
def IsSquarefree (n : ℕ) : Prop := Squarefree n

/-- The set of powers of 2: {1, 2, 4, 8, 16, ...} -/
def IsPowerOfTwo (n : ℕ) : Prop := ∃ k : ℕ, n = 2^k

/-- n can be written as squarefree + power of 2 -/
def IsSquarefreePlusPow2 (n : ℕ) : Prop :=
  ∃ (s p : ℕ), IsSquarefree s ∧ IsPowerOfTwo p ∧ n = s + p

/-! ## Basic Properties -/

/-- 1 is squarefree -/
theorem one_squarefree : IsSquarefree 1 := squarefree_one

/-- 1 is a power of 2 (2^0) -/
theorem one_is_pow2 : IsPowerOfTwo 1 := ⟨0, rfl⟩

/-- 2 is a power of 2 -/
theorem two_is_pow2 : IsPowerOfTwo 2 := ⟨1, rfl⟩

/-- Every prime is squarefree -/
theorem prime_squarefree {p : ℕ} (hp : Nat.Prime p) : IsSquarefree p :=
  hp.squarefree

/-! ## Small Examples -/

/-- 3 = 1 + 2 (squarefree + power of 2) -/
theorem three_works : IsSquarefreePlusPow2 3 :=
  ⟨1, 2, one_squarefree, two_is_pow2, rfl⟩

/-- 5 = 1 + 4 = 1 + 2² -/
theorem five_works : IsSquarefreePlusPow2 5 :=
  ⟨1, 4, one_squarefree, ⟨2, rfl⟩, rfl⟩

/-- 7 = 5 + 2 (5 is squarefree) -/
theorem seven_works : IsSquarefreePlusPow2 7 :=
  ⟨5, 2, by decide, two_is_pow2, rfl⟩

/-- 9 = 1 + 8 = 1 + 2³ -/
theorem nine_works : IsSquarefreePlusPow2 9 :=
  ⟨1, 8, one_squarefree, ⟨3, rfl⟩, rfl⟩

/-! ## Wieferich Primes -/

/-- A prime p is a Wieferich prime if 2^(p-1) ≡ 1 (mod p²) -/
def IsWieferichPrime (p : ℕ) : Prop :=
  Nat.Prime p ∧ 2^(p - 1) % (p^2) = 1

/-- The only known Wieferich primes are 1093 and 3511 -/
axiom known_wieferich_1093 : IsWieferichPrime 1093
axiom known_wieferich_3511 : IsWieferichPrime 3511

/-- It is conjectured that there are infinitely many non-Wieferich primes -/
def InfinitelyManyNonWieferich : Prop :=
  ∀ N : ℕ, ∃ p > N, Nat.Prime p ∧ ¬IsWieferichPrime p

/-! ## Main Conjecture -/

/-- Erdős Problem #11: Every odd n > 1 is squarefree + power of 2 -/
def Erdos11Conjecture : Prop :=
  ∀ n : ℕ, Odd n → n > 1 → IsSquarefreePlusPow2 n

/-- Weaker version: n not divisible by 4 -/
def Erdos11WeakConjecture : Prop :=
  ∀ n : ℕ, n > 1 → n % 4 ≠ 0 → IsSquarefreePlusPow2 n

/-- With two powers of 2 (Erdős thought this might be easier) -/
def IsSquarefreePlusTwoPow2 (n : ℕ) : Prop :=
  ∃ (s p q : ℕ), IsSquarefree s ∧ IsPowerOfTwo p ∧ IsPowerOfTwo q ∧ n = s + p + q

/-! ## Connection to Wieferich Primes (Granville-Soundararajan 1998) -/

/-- Granville-Soundararajan: Erdős 11 implies infinitely many non-Wieferich primes -/
axiom granville_soundararajan :
  Erdos11Conjecture → InfinitelyManyNonWieferich

/-! ## Computational Verification -/

/-- Hercher (2024): Verified for all odd n up to 2^50 -/
axiom hercher_verification :
  ∀ n : ℕ, Odd n → 1 < n → n < 2^50 → IsSquarefreePlusPow2 n

/-- Odlyzko: Earlier verification up to 10^7 -/
axiom odlyzko_verification :
  ∀ n : ℕ, Odd n → 1 < n → n < 10^7 → IsSquarefreePlusPow2 n

/-! ## Density Result -/

/-- Erdős proved the conjecture holds for almost all n -/
axiom erdos_almost_all :
  ∃ (S : Set ℕ), (∀ n ∈ S, Odd n → IsSquarefreePlusPow2 n) ∧
    -- S has density 1 among odd numbers
    Filter.Tendsto (fun N => (Finset.filter (· ∈ S) (Finset.range N)).card / N)
      Filter.atTop (nhds 1)
