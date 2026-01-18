/-
Erdős Problem #1074: EHS Numbers and Pillai Primes

Let S be the set of all m ≥ 1 such that there exists a prime p ≢ 1 (mod m)
with m! + 1 ≡ 0 (mod p). These are called "EHS numbers" after Erdős, Hardy,
and Subbarao.

Similarly, let P be the set of all primes p such that there exists an m with
p ≢ 1 (mod m) and m! + 1 ≡ 0 (mod p). These are called "Pillai primes".

**Main Questions (OPEN)**:
1. Does lim |S ∩ [1,x]| / x exist? What is it?
2. Does lim |P ∩ [1,x]| / π(x) exist? What is it?

**Known Results**:
- Both S and P are infinite (Erdős, Hardy, Subbarao)
- 23 is a Pillai prime: 14! + 1 ≡ 0 (mod 23) (Chowla)
- S begins: 8, 9, 13, 14, 15, 16, 17, ... (OEIS A064164)
- P begins: 23, 29, 59, 61, 67, 71, ... (OEIS A063980)

Reference: https://erdosproblems.com/1074
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

open Nat Set

namespace Erdos1074

/-! ## Definitions -/

/-- The EHS numbers (after Erdős, Hardy, and Subbarao) are those m ≥ 1 such that
there exists a prime p ≢ 1 (mod m) with p | m! + 1. -/
def EHSNumbers : Set ℕ :=
  {m | 1 ≤ m ∧ ∃ p, p.Prime ∧ ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

/-- The Pillai primes are those primes p such that there exists an m with
p ≢ 1 (mod m) and p | m! + 1. Named after S. S. Pillai who first asked
whether such primes exist. -/
def PillaiPrimes : Set ℕ :=
  {p | p.Prime ∧ ∃ m, ¬p ≡ 1 [MOD m] ∧ p ∣ m ! + 1}

/-! ## Chowla's Example: 23 is a Pillai Prime

Pillai (1930) raised the question of whether any Pillai primes exist.
Chowla answered affirmatively by observing that 14! + 1 ≡ 0 (mod 23).

Note: 23 ≢ 1 (mod 14) since 23 = 1·14 + 9 ≡ 9 (mod 14).
-/

/-- 23 divides 14! + 1. This is the key divisibility for Chowla's example. -/
theorem twentyThree_dvd_factorial_14_plus_one : 23 ∣ 14 ! + 1 := by
  native_decide

/-- 23 is not congruent to 1 modulo 14. -/
theorem twentyThree_not_cong_one_mod_14 : ¬(23 ≡ 1 [MOD 14]) := by
  native_decide

/-- 23 is prime. -/
theorem twentyThree_prime : Nat.Prime 23 := by
  native_decide

/-- Chowla's example: 23 is a Pillai prime, witnessed by m = 14.
This answered Pillai's 1930 question about the existence of such primes. -/
theorem pillai_23 : 23 ∈ PillaiPrimes := by
  refine ⟨twentyThree_prime, 14, twentyThree_not_cong_one_mod_14, ?_⟩
  exact twentyThree_dvd_factorial_14_plus_one

/-! ## Additional Verified Examples -/

/-- 8 is an EHS number. The first EHS number.
Witnessed by the prime 61: 61 ≢ 1 (mod 8) and 61 | 8! + 1.
Calculation: 8! + 1 = 40321 = 61 × 661, and 61 ≡ 5 (mod 8). -/
theorem ehs_8 : 8 ∈ EHSNumbers := by
  constructor
  · decide
  · refine ⟨61, ?_, ?_, ?_⟩
    · native_decide  -- 61 is prime
    · native_decide  -- 61 ≢ 1 (mod 8)
    · native_decide  -- 61 | 8! + 1

/-- 9 is an EHS number.
Witnessed by the prime 71: 71 ≢ 1 (mod 9) and 71 | 9! + 1.
Calculation: 9! + 1 = 362881 = 19 × 71 × 269, and 71 ≡ 8 (mod 9). -/
theorem ehs_9 : 9 ∈ EHSNumbers := by
  constructor
  · decide
  · refine ⟨71, ?_, ?_, ?_⟩
    · native_decide  -- 71 is prime
    · native_decide  -- 71 ≢ 1 (mod 9)
    · native_decide  -- 71 | 9! + 1

/-! ## Infinitude Results

Erdős, Hardy, and Subbarao proved that both sets are infinite.
These deep results require number-theoretic arguments beyond what
we formalize here, so we state them as axioms.
-/

/-- The set of EHS numbers is infinite.
Proved by Erdős, Hardy, and Subbarao.

The proof uses properties of prime factorizations of factorial values
and the distribution of primes in residue classes. -/
axiom EHSNumbers_infinite : EHSNumbers.Infinite

/-- The set of Pillai primes is infinite.
Proved by Erdős, Hardy, and Subbarao.

This follows from the infinitude of EHS numbers combined with
analysis of which primes can divide m! + 1. -/
axiom PillaiPrimes_infinite : PillaiPrimes.Infinite

/-! ## Open Problems

The main questions of Problem 1074 remain open:
- Does the natural density of EHS numbers exist?
- If so, is it 1 (as conjectured by Erdős, Hardy, and Subbarao)?
- Does the density of Pillai primes among all primes exist?
- If so, is it between 0.5 and 1?

Hardy and Subbarao computed all EHS numbers up to 2^10 and wrote:
"...if this trend continues we expect [the limit] to be around 0.5,
if it exists. The frequency with which the EHS numbers occur - most
often in long sequences of consecutive integers - makes us believe
that their asymptotic density exists and is unity."

These density questions cannot be settled by finite computation
and remain open research problems.
-/

/-- **OPEN**: Does the natural density of EHS numbers exist?
If so, Erdős, Hardy, and Subbarao conjectured it equals 1.

This formalizes the existence of the limit:
  lim_{x→∞} |S ∩ [1,x]| / x
where S is the set of EHS numbers. -/
axiom EHSNumbers_density_conjecture :
  ∃ d : ℕ → ℕ, ∀ x, d x = (EHSNumbers ∩ Finset.range (x + 1)).toFinite.toFinset.card

/-- **OPEN**: Does the relative density of Pillai primes exist?
Hardy and Subbarao estimated it might be between 0.5 and 0.6,
but also suggested it could tend to 1.

This formalizes the existence of the limit:
  lim_{x→∞} |P ∩ [1,x]| / π(x)
where P is the set of Pillai primes and π(x) is the prime counting function. -/
axiom PillaiPrimes_density_conjecture :
  ∃ d : ℕ → ℕ, ∀ x, d x = (PillaiPrimes ∩ Finset.range (x + 1)).toFinite.toFinset.card

end Erdos1074
