/-
# Twin Primes

A twin prime pair is (p, p+2) where both p and p+2 are prime.
Examples: (3,5), (5,7), (11,13), (17,19), (29,31), ...

**Status**: DEEP DIVE
- Defines twin primes formally
- Proves structural constraints (mod 6)
- Verifies small examples
- States twin prime conjecture

**Key Result**: For p > 3, if (p, p+2) are both prime, then p ≡ 5 (mod 6).
Equivalently, twin primes > 3 have the form (6k-1, 6k+1).

**What's NOT proven**: The twin prime conjecture (infinitely many twin primes)
is a famous unsolved problem. We state it as an axiom.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace TwinPrimes

/-!
## Definition of Twin Primes
-/

/-- A natural number p forms a twin prime pair if both p and p+2 are prime -/
def IsTwinPrimePair (p : ℕ) : Prop := Nat.Prime p ∧ Nat.Prime (p + 2)

/-- The twin prime conjecture: there are infinitely many twin prime pairs -/
def TwinPrimeConjecture : Prop := ∀ N : ℕ, ∃ p : ℕ, p > N ∧ IsTwinPrimePair p

/-!
## Small Examples

We verify several twin prime pairs computationally.
-/

/-- (3, 5) is a twin prime pair -/
theorem twin_3_5 : IsTwinPrimePair 3 := by
  constructor
  · exact Nat.prime_three
  · decide

/-- (5, 7) is a twin prime pair -/
theorem twin_5_7 : IsTwinPrimePair 5 := by
  constructor <;> decide

/-- (11, 13) is a twin prime pair -/
theorem twin_11_13 : IsTwinPrimePair 11 := by
  constructor <;> decide

/-- (17, 19) is a twin prime pair -/
theorem twin_17_19 : IsTwinPrimePair 17 := by
  constructor <;> decide

/-- (29, 31) is a twin prime pair -/
theorem twin_29_31 : IsTwinPrimePair 29 := by
  constructor <;> decide

/-- (41, 43) is a twin prime pair -/
theorem twin_41_43 : IsTwinPrimePair 41 := by
  constructor <;> decide

/-!
## Structure Theorem: Twin Primes and Residue Classes

For p > 3, if (p, p+2) are both prime, then p ≡ 5 (mod 6).

**Proof idea**:
- All primes > 3 are ≡ 1 or 5 (mod 6)
- If p ≡ 1 (mod 6), then p+2 ≡ 3 (mod 6), divisible by 3
- So p+2 can't be prime (unless p+2 = 3, impossible for p > 1)
- Therefore p ≡ 5 (mod 6)
-/

/-- Primes greater than 3 are not divisible by 2 -/
theorem prime_gt_three_not_even (p : ℕ) (hp : Nat.Prime p) (h3 : p > 3) : ¬ 2 ∣ p := by
  intro hdiv
  have h2 : 2 = p := (Nat.Prime.eq_one_or_self_of_dvd hp 2 hdiv).resolve_left (by decide)
  omega

/-- Primes greater than 3 are not divisible by 3 -/
theorem prime_gt_three_not_div_three (p : ℕ) (hp : Nat.Prime p) (h3 : p > 3) : ¬ 3 ∣ p := by
  intro hdiv
  have h3' : 3 = p := (Nat.Prime.eq_one_or_self_of_dvd hp 3 hdiv).resolve_left (by decide)
  omega

/-- p > 3 prime implies p mod 6 ∈ {1, 5} -/
theorem prime_mod_six (p : ℕ) (hp : Nat.Prime p) (h3 : p > 3) : p % 6 = 1 ∨ p % 6 = 5 := by
  have hne0 : p % 6 ≠ 0 := by
    intro h
    have : 6 ∣ p := Nat.dvd_of_mod_eq_zero h
    have : 2 ∣ p := Nat.dvd_trans (by decide : 2 ∣ 6) this
    exact prime_gt_three_not_even p hp h3 this
  have hne2 : p % 6 ≠ 2 := by
    intro h
    have : p % 2 = 0 := by omega
    have : 2 ∣ p := Nat.dvd_of_mod_eq_zero this
    exact prime_gt_three_not_even p hp h3 this
  have hne3 : p % 6 ≠ 3 := by
    intro h
    have : p % 3 = 0 := by omega
    have : 3 ∣ p := Nat.dvd_of_mod_eq_zero this
    exact prime_gt_three_not_div_three p hp h3 this
  have hne4 : p % 6 ≠ 4 := by
    intro h
    have : p % 2 = 0 := by omega
    have : 2 ∣ p := Nat.dvd_of_mod_eq_zero this
    exact prime_gt_three_not_even p hp h3 this
  have hlt : p % 6 < 6 := Nat.mod_lt p (by decide)
  omega

/-- If p ≡ 1 (mod 6), then p + 2 ≡ 3 (mod 6), so 3 ∣ (p + 2) -/
theorem mod_one_implies_plus_two_div_three (p : ℕ) (h : p % 6 = 1) : 3 ∣ (p + 2) := by
  have : (p + 2) % 6 = 3 := by omega
  have : (p + 2) % 3 = 0 := by omega
  exact Nat.dvd_of_mod_eq_zero this

/-- **Structure Theorem**: For p > 3, if (p, p+2) are twin primes, then p ≡ 5 (mod 6) -/
theorem twin_prime_mod_six (p : ℕ) (hp : IsTwinPrimePair p) (h3 : p > 3) : p % 6 = 5 := by
  obtain ⟨hp1, hp2⟩ := hp
  rcases prime_mod_six p hp1 h3 with h1 | h5
  · -- Case: p ≡ 1 (mod 6)
    -- Then p + 2 ≡ 3 (mod 6), so 3 | (p + 2)
    have hdiv : 3 ∣ (p + 2) := mod_one_implies_plus_two_div_three p h1
    -- Since p + 2 is prime and 3 | (p + 2), we must have p + 2 = 3
    have heq : 3 = p + 2 := (Nat.Prime.eq_one_or_self_of_dvd hp2 3 hdiv).resolve_left (by decide)
    -- But p > 3 implies p + 2 > 5, contradiction
    omega
  · exact h5

/-- Corollary: twin primes > 3 have form (6k-1, 6k+1) -/
theorem twin_prime_form (p : ℕ) (hp : IsTwinPrimePair p) (h3 : p > 3) :
    ∃ k : ℕ, k ≥ 1 ∧ p = 6 * k - 1 ∧ p + 2 = 6 * k + 1 := by
  have hmod : p % 6 = 5 := twin_prime_mod_six p hp h3
  -- p ≡ 5 (mod 6) means p + 1 ≡ 0 (mod 6)
  have hdiv : 6 ∣ (p + 1) := by
    have : (p + 1) % 6 = 0 := by omega
    exact Nat.dvd_of_mod_eq_zero this
  obtain ⟨k, hk⟩ := hdiv
  use k
  have hk_pos : k ≥ 1 := by
    by_contra hcon
    push_neg at hcon
    have hk0 : k = 0 := by omega
    rw [hk0] at hk
    omega
  refine ⟨hk_pos, ?_, ?_⟩
  · omega
  · omega

/-!
## The Conjecture

The twin prime conjecture remains unsolved. We state it as an axiom.
-/

/-- The Twin Prime Conjecture: there are infinitely many twin prime pairs -/
axiom twin_prime_conjecture : TwinPrimeConjecture

/-- There exists a twin prime pair greater than any bound -/
theorem exists_twin_prime_gt (N : ℕ) : ∃ p : ℕ, p > N ∧ IsTwinPrimePair p :=
  twin_prime_conjecture N

/-!
## Additional Results
-/

/-- 2 is not part of a twin prime pair (since 4 is not prime) -/
theorem two_not_twin : ¬ IsTwinPrimePair 2 := by
  intro ⟨_, h4⟩
  have : (4 : ℕ) = 2 * 2 := by decide
  have : ¬ Nat.Prime 4 := by decide
  exact this h4

/-- 1 is not part of a twin prime pair (since 1 is not prime) -/
theorem one_not_twin : ¬ IsTwinPrimePair 1 := by
  intro ⟨h1, _⟩
  exact Nat.not_prime_one h1

/-- 0 is not part of a twin prime pair -/
theorem zero_not_twin : ¬ IsTwinPrimePair 0 := by
  intro ⟨h0, _⟩
  exact Nat.not_prime_zero h0

end TwinPrimes
