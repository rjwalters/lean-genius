/-
# Sophie Germain Primes

A prime p is a Sophie Germain prime if 2p + 1 is also prime.
The prime 2p + 1 is called a "safe prime."

Examples: 2, 3, 5, 11, 23, 29, 41, 53, 83, 89, ...
- p = 2: 2*2+1 = 5 (prime) ✓
- p = 11: 2*11+1 = 23 (prime) ✓
- p = 23: 2*23+1 = 47 (prime) ✓

**Status**: DEEP DIVE
- Defines Sophie Germain primes formally
- Proves structural constraints (mod 6)
- Verifies small examples
- States the Sophie Germain prime conjecture

**Key Result**: For p > 3, if p is a Sophie Germain prime, then p ≡ 5 (mod 6).
Equivalently, Sophie Germain primes > 3 have the form 6k - 1.

**What's NOT proven**: The Sophie Germain prime conjecture (infinitely many
Sophie Germain primes) is a famous unsolved problem. We state it as an axiom.
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace SophieGermain

/-!
## Definition of Sophie Germain Primes
-/

/-- A natural number p is a Sophie Germain prime if both p and 2p+1 are prime -/
def IsSophieGermainPrime (p : ℕ) : Prop := Nat.Prime p ∧ Nat.Prime (2 * p + 1)

/-- The safe prime corresponding to a Sophie Germain prime p is q = 2p + 1 -/
def SafePrime (p : ℕ) : ℕ := 2 * p + 1

/-- A safe prime is a prime q such that (q-1)/2 is also prime -/
def IsSafePrime (q : ℕ) : Prop := Nat.Prime q ∧ q % 2 = 1 ∧ Nat.Prime ((q - 1) / 2)

/-- The Sophie Germain prime conjecture: there are infinitely many Sophie Germain primes -/
def SophieGermainConjecture : Prop := ∀ N : ℕ, ∃ p : ℕ, p > N ∧ IsSophieGermainPrime p

/-!
## Small Examples

We verify several Sophie Germain primes computationally.
-/

/-- 2 is a Sophie Germain prime (2*2+1 = 5 is prime) -/
theorem sg_2 : IsSophieGermainPrime 2 := by
  constructor
  · exact Nat.prime_two
  · decide

/-- 3 is a Sophie Germain prime (2*3+1 = 7 is prime) -/
theorem sg_3 : IsSophieGermainPrime 3 := by
  constructor
  · exact Nat.prime_three
  · decide

/-- 5 is a Sophie Germain prime (2*5+1 = 11 is prime) -/
theorem sg_5 : IsSophieGermainPrime 5 := by
  constructor <;> decide

/-- 11 is a Sophie Germain prime (2*11+1 = 23 is prime) -/
theorem sg_11 : IsSophieGermainPrime 11 := by
  constructor <;> decide

/-- 23 is a Sophie Germain prime (2*23+1 = 47 is prime) -/
theorem sg_23 : IsSophieGermainPrime 23 := by
  constructor <;> decide

/-- 29 is a Sophie Germain prime (2*29+1 = 59 is prime) -/
theorem sg_29 : IsSophieGermainPrime 29 := by
  constructor <;> decide

/-- 41 is a Sophie Germain prime (2*41+1 = 83 is prime) -/
theorem sg_41 : IsSophieGermainPrime 41 := by
  constructor <;> decide

/-- 53 is a Sophie Germain prime (2*53+1 = 107 is prime) -/
theorem sg_53 : IsSophieGermainPrime 53 := by
  constructor <;> decide

/-- 83 is a Sophie Germain prime (2*83+1 = 167 is prime) -/
theorem sg_83 : IsSophieGermainPrime 83 := by
  constructor <;> decide

/-- 89 is a Sophie Germain prime (2*89+1 = 179 is prime) -/
theorem sg_89 : IsSophieGermainPrime 89 := by
  constructor <;> decide

/-!
## Non-examples

Some primes are NOT Sophie Germain primes.
-/

/-- 7 is NOT a Sophie Germain prime (2*7+1 = 15 = 3*5) -/
theorem not_sg_7 : ¬ IsSophieGermainPrime 7 := by
  intro ⟨_, h15⟩
  have : ¬ Nat.Prime 15 := by decide
  exact this h15

/-- 13 is NOT a Sophie Germain prime (2*13+1 = 27 = 3³) -/
theorem not_sg_13 : ¬ IsSophieGermainPrime 13 := by
  intro ⟨_, h27⟩
  have : ¬ Nat.Prime 27 := by decide
  exact this h27

/-- 17 is NOT a Sophie Germain prime (2*17+1 = 35 = 5*7) -/
theorem not_sg_17 : ¬ IsSophieGermainPrime 17 := by
  intro ⟨_, h35⟩
  have : ¬ Nat.Prime 35 := by decide
  exact this h35

/-- 19 is NOT a Sophie Germain prime (2*19+1 = 39 = 3*13) -/
theorem not_sg_19 : ¬ IsSophieGermainPrime 19 := by
  intro ⟨_, h39⟩
  have : ¬ Nat.Prime 39 := by decide
  exact this h39

/-!
## Structure Theorem: Sophie Germain Primes and Residue Classes

For p > 3, if p is a Sophie Germain prime, then p ≡ 5 (mod 6).

**Proof idea**:
- All primes > 3 are ≡ 1 or 5 (mod 6)
- If p ≡ 1 (mod 6), then 2p+1 ≡ 3 (mod 6), divisible by 3
- So 2p+1 can't be prime (unless 2p+1 = 3, impossible for p ≥ 1)
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

/-- If p ≡ 1 (mod 6), then 2p + 1 ≡ 3 (mod 6), so 3 ∣ (2p + 1) -/
theorem mod_one_implies_two_p_plus_one_div_three (p : ℕ) (h : p % 6 = 1) : 3 ∣ (2 * p + 1) := by
  have : (2 * p + 1) % 6 = 3 := by omega
  have : (2 * p + 1) % 3 = 0 := by omega
  exact Nat.dvd_of_mod_eq_zero this

/-- **Structure Theorem**: For p > 3, if p is a Sophie Germain prime, then p ≡ 5 (mod 6) -/
theorem sophie_germain_mod_six (p : ℕ) (hp : IsSophieGermainPrime p) (h3 : p > 3) : p % 6 = 5 := by
  obtain ⟨hp1, hp2⟩ := hp
  rcases prime_mod_six p hp1 h3 with h1 | h5
  · -- Case: p ≡ 1 (mod 6)
    -- Then 2p + 1 ≡ 3 (mod 6), so 3 | (2p + 1)
    have hdiv : 3 ∣ (2 * p + 1) := mod_one_implies_two_p_plus_one_div_three p h1
    -- Since 2p + 1 is prime and 3 | (2p + 1), we must have 2p + 1 = 3
    have heq : 3 = 2 * p + 1 := (Nat.Prime.eq_one_or_self_of_dvd hp2 3 hdiv).resolve_left (by decide)
    -- But p > 3 implies 2p + 1 > 7, contradiction
    omega
  · exact h5

/-- Corollary: Sophie Germain primes > 3 have form 6k - 1 -/
theorem sophie_germain_form (p : ℕ) (hp : IsSophieGermainPrime p) (h3 : p > 3) :
    ∃ k : ℕ, k ≥ 1 ∧ p = 6 * k - 1 := by
  have hmod : p % 6 = 5 := sophie_germain_mod_six p hp h3
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
  refine ⟨hk_pos, ?_⟩
  omega

/-!
## Safe Prime Structure

A safe prime q = 2p + 1 > 7 also has structural constraints.
-/

/-- For a Sophie Germain prime p > 3, the safe prime 2p+1 ≡ 11 (mod 12) -/
theorem safe_prime_mod_twelve (p : ℕ) (hp : IsSophieGermainPrime p) (h3 : p > 3) :
    (2 * p + 1) % 12 = 11 := by
  have hmod6 : p % 6 = 5 := sophie_germain_mod_six p hp h3
  -- p ≡ 5 (mod 6) means p = 6k + 5 for some k
  -- So 2p + 1 = 12k + 11 ≡ 11 (mod 12)
  omega

/-- The safe prime of a Sophie Germain prime is odd -/
theorem safe_prime_odd (p : ℕ) (_hp : IsSophieGermainPrime p) : (2 * p + 1) % 2 = 1 := by
  omega

/-- Relationship: p is Sophie Germain iff 2p+1 is a safe prime with (2p+1-1)/2 = p prime -/
theorem sophie_germain_iff_safe (p : ℕ) :
    IsSophieGermainPrime p ↔ Nat.Prime p ∧ IsSafePrime (2 * p + 1) := by
  constructor
  · intro ⟨hp, hq⟩
    refine ⟨hp, hq, ?_, ?_⟩
    · omega
    · simp only [Nat.add_sub_cancel]
      have : 2 * p / 2 = p := Nat.mul_div_cancel_left p (by decide : 0 < 2)
      rw [this]
      exact hp
  · intro ⟨hp, hq, _, _⟩
    exact ⟨hp, hq⟩

/-!
## The Conjecture

The Sophie Germain prime conjecture remains unsolved. We state it as an axiom.
-/

/-- The Sophie Germain Prime Conjecture: there are infinitely many Sophie Germain primes -/
axiom sophie_germain_conjecture : SophieGermainConjecture

/-- There exists a Sophie Germain prime greater than any bound -/
theorem exists_sophie_germain_gt (N : ℕ) : ∃ p : ℕ, p > N ∧ IsSophieGermainPrime p :=
  sophie_germain_conjecture N

/-!
## Additional Results
-/

/-- 1 is not a Sophie Germain prime (since 1 is not prime) -/
theorem one_not_sg : ¬ IsSophieGermainPrime 1 := by
  intro ⟨h1, _⟩
  exact Nat.not_prime_one h1

/-- 0 is not a Sophie Germain prime -/
theorem zero_not_sg : ¬ IsSophieGermainPrime 0 := by
  intro ⟨h0, _⟩
  exact Nat.not_prime_zero h0

/-- If p is a Sophie Germain prime, then p ≥ 2 -/
theorem sophie_germain_ge_two (p : ℕ) (hp : IsSophieGermainPrime p) : p ≥ 2 := by
  exact hp.1.two_le

/-- If p is a Sophie Germain prime, then 2p+1 > p -/
theorem safe_prime_gt (p : ℕ) (hp : IsSophieGermainPrime p) : 2 * p + 1 > p := by
  have : p ≥ 2 := sophie_germain_ge_two p hp
  omega

/-- A Sophie Germain prime chain: 2 → 5 → 11 → 23 → 47 (each is 2p+1 of previous) -/
theorem sg_chain_2_5_11_23 : IsSophieGermainPrime 2 ∧ IsSophieGermainPrime 5 ∧
    IsSophieGermainPrime 11 ∧ IsSophieGermainPrime 23 := by
  refine ⟨sg_2, sg_5, sg_11, sg_23⟩

/-- 47 is prime (end of the chain) -/
theorem prime_47 : Nat.Prime 47 := by decide

/-- 47 is NOT a Sophie Germain prime (2*47+1 = 95 = 5*19) -/
theorem not_sg_47 : ¬ IsSophieGermainPrime 47 := by
  intro ⟨_, h95⟩
  have : ¬ Nat.Prime 95 := by decide
  exact this h95

end SophieGermain
