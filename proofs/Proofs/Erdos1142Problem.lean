/-
# Erdős Problem #1142 — Primes of the form n − 2^k

**Question**: Are there infinitely many n (or any n > 105) such that
n − 2^k is prime for all 1 < 2^k < n?

## Status: OPEN

## Known Results

- The only known values are n ∈ {4, 7, 15, 21, 45, 75, 105} (OEIS A039669).
- Mientka & Weitzenkamp (1969) verified no other n ≤ 2^44 satisfy this.
- Vaughan (1973) showed the count of such n up to N is extremely sparse.
- Erdős conjectured the number of 1 < 2^k < n for which n − 2^k is prime
  is o(log n).

## Related Problems

- #236: Stronger conjecture about o(log n) prime differences.

*Reference:* Va99 §1.7, [erdosproblems.com/1142](https://www.erdosproblems.com/1142)
-/

import Mathlib.Tactic
import Mathlib.Data.Nat.Prime.Basic

open Finset

-- ## Core Definitions

/-- The set of powers of 2 strictly between 1 and n.
    These are {2^k | k ≥ 1, 2^k < n} = {2, 4, 8, ..., 2^⌊log₂(n-1)⌋}.
    Defined as image of the exponent range for clean decidability. -/
def powersOfTwoBetween (n : ℕ) : Finset ℕ :=
  ((Finset.range n).filter (fun k => 1 ≤ k ∧ 2 ^ k < n)).image (2 ^ ·)

/-- An integer n satisfies the Erdős 1142 property if n − 2^k is prime
for every power of 2 with 1 < 2^k < n. We also require at least one
such power of 2 (i.e., n ≥ 4, since 2^1 = 2 < 4). -/
def SatisfiesErdos1142 (n : ℕ) : Prop :=
  (powersOfTwoBetween n).Nonempty ∧
    ∀ m ∈ powersOfTwoBetween n, (n - m).Prime

instance (n : ℕ) : Decidable (SatisfiesErdos1142 n) := by
  unfold SatisfiesErdos1142
  exact inferInstance

-- ## Verification of Known Values

-- The known values satisfying the property: 4, 7, 15, 21, 45, 75, 105.

-- n = 4: powers of 2 in (1, 4) = {2}. 4 - 2 = 2 (prime). ✓
theorem erdos1142_value_4 : SatisfiesErdos1142 4 := by native_decide

-- n = 7: powers of 2 in (1, 7) = {2, 4}. 7 - 2 = 5, 7 - 4 = 3. Both prime. ✓
theorem erdos1142_value_7 : SatisfiesErdos1142 7 := by native_decide

-- n = 15: powers of 2 in (1, 15) = {2, 4, 8}. 15 - 2 = 13, 15 - 4 = 11, 15 - 8 = 7. ✓
theorem erdos1142_value_15 : SatisfiesErdos1142 15 := by native_decide

-- n = 21: powers of 2 in (1, 21) = {2, 4, 8, 16}. 21 - 2 = 19, 21 - 4 = 17,
-- 21 - 8 = 13, 21 - 16 = 5. All prime. ✓
theorem erdos1142_value_21 : SatisfiesErdos1142 21 := by native_decide

-- n = 45: powers of 2 in (1, 45) = {2, 4, 8, 16, 32}.
-- 45 - 2 = 43, 45 - 4 = 41, 45 - 8 = 37, 45 - 16 = 29, 45 - 32 = 13. ✓
theorem erdos1142_value_45 : SatisfiesErdos1142 45 := by native_decide

-- n = 75: powers of 2 in (1, 75) = {2, 4, 8, 16, 32, 64}.
-- 75 - 2 = 73, 75 - 4 = 71, 75 - 8 = 67, 75 - 16 = 59, 75 - 32 = 43, 75 - 64 = 11. ✓
theorem erdos1142_value_75 : SatisfiesErdos1142 75 := by native_decide

-- n = 105: powers of 2 in (1, 105) = {2, 4, 8, 16, 32, 64}.
-- 105 - 2 = 103, 105 - 4 = 101, 105 - 8 = 97, 105 - 16 = 89,
-- 105 - 32 = 73, 105 - 64 = 41. All prime. ✓
theorem erdos1142_value_105 : SatisfiesErdos1142 105 := by native_decide

-- ## Non-Examples (counterexamples to being in the set)

-- n = 6: powers of 2 in (1, 6) = {2, 4}. 6 - 4 = 2 (prime), but 6 - 2 = 4 (not prime). ✗
theorem erdos1142_not_6 : ¬SatisfiesErdos1142 6 := by native_decide

-- n = 9: 9 - 8 = 1 (not prime). ✗
theorem erdos1142_not_9 : ¬SatisfiesErdos1142 9 := by native_decide

-- n = 10: 10 - 2 = 8 (not prime). ✗
theorem erdos1142_not_10 : ¬SatisfiesErdos1142 10 := by native_decide

-- ## Structural Properties

/-- Helper: 2 is in powersOfTwoBetween n whenever n ≥ 3. -/
private theorem two_mem_powersOfTwoBetween {n : ℕ} (hn : n ≥ 3) :
    2 ∈ powersOfTwoBetween n := by
  simp only [powersOfTwoBetween, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  exact ⟨1, ⟨by omega, by omega, by omega⟩, by norm_num⟩

/-- If n satisfies the property, then n ≥ 4 (there must be at least one power of 2
in (1, n), namely 2 itself). -/
theorem erdos1142_ge_4 {n : ℕ} (hn : SatisfiesErdos1142 n) : n ≥ 4 := by
  obtain ⟨hne, hprime⟩ := hn
  -- Get some m in the set to establish n ≥ 3
  obtain ⟨m, hm⟩ := hne
  simp only [powersOfTwoBetween, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hm
  obtain ⟨k, ⟨_, hk1, hk2⟩, _⟩ := hm
  -- k ≥ 1, 2^k < n, so n ≥ 3
  have hn3 : n ≥ 3 := by
    have : 2 ^ k ≥ 2 := Nat.one_le_pow k 2 (by norm_num) |>.trans_lt (by omega) |>.le
    omega
  have h2_mem := two_mem_powersOfTwoBetween hn3
  have h_ge2 := (hprime 2 h2_mem).two_le
  omega

/-- For n satisfying the property, n - 2 is prime (since 2 ∈ powersOfTwoBetween n). -/
theorem erdos1142_n_minus_2_prime {n : ℕ} (hn : SatisfiesErdos1142 n) :
    (n - 2).Prime := by
  have hge4 := erdos1142_ge_4 hn
  exact hn.2 2 (two_mem_powersOfTwoBetween (by omega))

/-- Every number satisfying the property is odd, except for 4.
If n > 4 and n is even, then n - 2 is even and ≥ 4, hence not prime. -/
theorem erdos1142_odd_or_4 {n : ℕ} (hn : SatisfiesErdos1142 n) (hn4 : n ≠ 4) :
    Odd n := by
  have hge4 := erdos1142_ge_4 hn
  have hge5 : n ≥ 5 := by omega
  by_contra h_not_odd
  rw [Nat.not_odd_iff_even] at h_not_odd
  have h_prime := erdos1142_n_minus_2_prime hn
  -- n is even and ≥ 6 (even, ≥ 5 → ≥ 6), so n - 2 is even and ≥ 4
  -- 2 divides n - 2 since n is even
  have h_two_dvd : 2 ∣ (n - 2) := by
    obtain ⟨k, hk⟩ := h_not_odd
    exact ⟨k - 1, by omega⟩
  -- If n - 2 is prime and 2 ∣ (n - 2), then 2 = 1 ∨ 2 = n - 2
  rcases h_prime.eq_one_or_self_of_dvd 2 h_two_dvd with h1 | h2
  · -- 2 = 1 is absurd
    omega
  · -- 2 = n - 2, so n = 4, but n ≠ 4
    omega

/-- n must be ≡ 1 (mod 2) for n > 4: the property forces n to be odd. -/
theorem erdos1142_mod2 {n : ℕ} (hn : SatisfiesErdos1142 n) (hn4 : n > 4) :
    n % 2 = 1 := by
  exact Nat.odd_iff.mp (erdos1142_odd_or_4 hn (by omega))

-- Note: the modular constraint is actually weaker than 3 mod 4.
-- The real constraint comes from n being odd and n - 2^k being prime for each k.

-- ## The Conjecture

/-- **Erdős Problem #1142 (OPEN).**
Are there infinitely many n such that n − 2^k is prime for all 1 < 2^k < n?

The known values are {4, 7, 15, 21, 45, 75, 105}. No others have been found
up to 2^44 (Mientka & Weitzenkamp, 1969). -/
def erdos_1142_conjecture : Prop :=
  Set.Infinite {n : ℕ | SatisfiesErdos1142 n}

/-- **Stronger conjecture (Erdős).**
The number of k with 1 < 2^k < n for which n − 2^k is prime is o(log n).
This would imply that the "density" of prime differences decreases
as n grows, suggesting finiteness of the set.

Formally: for every ε > 0, for all sufficiently large n, the count of k
with 1 ≤ k, 2^k < n, and n - 2^k prime is at most ε · log₂(n). -/
def erdos_1142_stronger_conjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, n ≥ N →
    (((Finset.range (Nat.log 2 n + 1)).filter
      (fun k => k ≥ 1 ∧ 2 ^ k < n ∧ (n - 2 ^ k).Prime)).card : ℝ)
    ≤ ε * (Nat.log 2 n : ℝ)

-- ## Completeness of Known Values up to a Bound

/-- There are exactly 7 values satisfying the property up to 105. -/
theorem erdos1142_complete_le_105 :
    ((Finset.range 106).filter SatisfiesErdos1142) =
      {4, 7, 15, 21, 45, 75, 105} := by
  native_decide

-- ## Relationship to Problem #236

/-- Problem #236 asks: is the count of prime differences o(log n)?
If this stronger conjecture holds, then eventually no n can have
ALL ⌊log₂ n⌋ differences being prime, suggesting the set is finite. -/
-- TODO: stronger_implies_eventually_not_all_prime
-- Key idea: Take ε = 1/2. For large n, prime_count ≤ (1/2)·log₂(n).
-- But SatisfiesErdos1142 n requires ALL ⌊log₂(n-1)⌋ differences to be prime.
-- For n ≥ 8, ⌊log₂(n-1)⌋ ≥ 2 > (1/2)·log₂(n), contradiction.
-- Proof blocked by: Nat.log / Finset.card / ℝ arithmetic bridge.

-- TODO: powersOfTwoBetween_card
-- (powersOfTwoBetween n).card = Nat.log 2 (n - 1) for n ≥ 4
-- Proof blocked by: bijection between filter set and Finset.range (Nat.log 2 (n-1))
