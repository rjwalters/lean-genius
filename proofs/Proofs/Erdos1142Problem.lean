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

/-- The set of powers of 2 strictly between 1 and n. These are the values 2^k
with k ≥ 1 and 2^k < n. -/
def powersOfTwoBetween (n : ℕ) : Finset ℕ :=
  (Finset.range n).filter (fun m => m ≥ 2 ∧ m.isPowerOfTwo)

/-- An integer n satisfies the Erdős 1142 property if n − 2^k is prime
for every power of 2 with 1 < 2^k < n. We also require at least one
such power of 2 (i.e., n ≥ 4, since 2^1 = 2 < 4). -/
def SatisfiesErdos1142 (n : ℕ) : Prop :=
  (powersOfTwoBetween n).Nonempty ∧
    ∀ m ∈ powersOfTwoBetween n, (n - m).Prime

/-- Boolean version for computation. -/
def satisfiesErdos1142Bool (n : ℕ) : Bool :=
  let pows := powersOfTwoBetween n
  !pows.val.isEmpty && pows.val.all (fun m => (n - m).Prime)

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

/-- Every number satisfying the property is odd, except for 4.
Proof: If n > 4 and n is even, then 2 ∈ powersOfTwoBetween n,
and n - 2 is even and > 2, hence not prime. -/
theorem erdos1142_odd_or_4 {n : ℕ} (hn : SatisfiesErdos1142 n) (hn4 : n ≠ 4) :
    Odd n := by
  sorry

/-- If n satisfies the property, then n ≥ 4 (there must be at least one power of 2
in (1, n), namely 2 itself). -/
theorem erdos1142_ge_4 {n : ℕ} (hn : SatisfiesErdos1142 n) : n ≥ 4 := by
  sorry

/-- For n satisfying the property with n > 4, we need n - 2 to be prime.
Since n is odd (by the above), n - 2 is also odd. -/
theorem erdos1142_n_minus_2_prime {n : ℕ} (hn : SatisfiesErdos1142 n) :
    (n - 2).Prime := by
  sorry

/-- n must be ≡ 1 (mod 2) for n > 4: the property forces n to be odd. -/
theorem erdos1142_mod2 {n : ℕ} (hn : SatisfiesErdos1142 n) (hn4 : n > 4) :
    n % 2 = 1 := by
  sorry

/-- If n satisfies the property, then n must be ≡ 3 (mod 4) or n = 4.
Proof: If n > 4, then 4 ∈ powersOfTwoBetween n. If n ≡ 1 (mod 4),
then n - 4 ≡ 1 (mod 4) is odd but could be ≡ 1 (mod 2), which is fine.
However, we also need n ≡ 1 (mod 2), so n is odd.
Checking: n ≡ 1 (mod 4) means n - 4 ≡ -3 ≡ 1 (mod 4).
n ≡ 3 (mod 4) means n - 4 ≡ -1 ≡ 3 (mod 4).
Both are possible; we need n - 4 to be prime.
Actually, n ≡ 3 (mod 4) forces n - 2 ≡ 1 (mod 4), which can be prime. -/
-- Note: the modular constraint is actually weaker than 3 mod 4.
-- The real constraint comes from n being odd and n - 2^k being prime for each k.

/-- The number of powers of 2 below n grows logarithmically.
Specifically, |{2^k : 1 < 2^k < n}| = ⌊log₂ n⌋ for n ≥ 2. -/
theorem powersOfTwoBetween_card (n : ℕ) (hn : n ≥ 4) :
    (powersOfTwoBetween n).card = Nat.log 2 n := by
  sorry

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
theorem stronger_implies_eventually_not_all_prime :
    erdos_1142_stronger_conjecture →
      ∃ N : ℕ, ∀ n : ℕ, n ≥ N → ¬SatisfiesErdos1142 n := by
  sorry
