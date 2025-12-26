import Archive.Wiedijk100Theorems.PerfectNumbers
import Mathlib.Tactic

/-!
# The Perfect Number Theorem (Euclid-Euler)

## What This Proves
A number is *perfect* if it equals the sum of its proper divisors.
For example: 6 = 1 + 2 + 3, and 28 = 1 + 2 + 4 + 7 + 14.

The Euclid-Euler Theorem completely characterizes even perfect numbers:

**Euclid's Direction (300 BCE)**: If 2ᵖ - 1 is prime (a Mersenne prime),
then 2ᵖ⁻¹(2ᵖ - 1) is perfect.

**Euler's Direction (1747)**: Every even perfect number has this form.

## Approach
- **Foundation (from Mathlib):** We use `Archive.Wiedijk100Theorems.PerfectNumbers`
  which provides the complete Euclid-Euler theorem.
- **Original Contributions:** Pedagogical wrapper theorems with examples of
  the first four perfect numbers (6, 28, 496, 8128).
- **Proof Techniques Demonstrated:** Working with divisor sums, multiplicative
  arithmetic functions, and Mersenne primes.

## Status
- [x] Complete proof (Euclid direction)
- [x] Complete proof (Euler direction)
- [x] Uses Mathlib for main results
- [x] Examples for 6, 28, 496, 8128
- [ ] Incomplete (has sorries)

## Mathlib Dependencies
- `Nat.Perfect` : Definition of perfect numbers via σ(n) = 2n
- `mersenne` : Mersenne numbers 2ᵖ - 1
- `ArithmeticFunction.sigma` : Sum of divisors function
- `Archive/Wiedijk100Theorems/PerfectNumbers.lean` : Complete proofs

## Historical Note
Euclid proved in Elements Book IX, Proposition 36 that Mersenne primes yield
perfect numbers. Euler proved the converse 2000 years later, showing these
are the ONLY even perfect numbers. Whether odd perfect numbers exist remains
one of the oldest unsolved problems in mathematics!

## Known Perfect Numbers
The first ten perfect numbers correspond to Mersenne primes 2ᵖ-1 for:
p = 2, 3, 5, 7, 13, 17, 19, 31, 61, 89, ...

| n  | Perfect Number | Mersenne Prime |
|----|----------------|----------------|
| 1  | 6              | 2² - 1 = 3     |
| 2  | 28             | 2³ - 1 = 7     |
| 3  | 496            | 2⁵ - 1 = 31    |
| 4  | 8128           | 2⁷ - 1 = 127   |

## Wiedijk's 100 Theorems: #70
-/

namespace PerfectNumbers

open ArithmeticFunction Finset Nat

/-! ## Core Definition of Perfect Numbers -/

/-- A number is *perfect* if the sum of ALL divisors is twice n.
    Equivalently, the sum of PROPER divisors equals n.

    For example, for n = 6:
    - All divisors: 1, 2, 3, 6  → sum = 12 = 2 × 6 ✓
    - Proper divisors: 1, 2, 3  → sum = 6 ✓ -/
theorem perfect_iff_divisor_sum (n : ℕ) (hn : 0 < n) :
    n.Perfect ↔ ∑ i ∈ n.divisors, i = 2 * n :=
  Nat.perfect_iff_sum_divisors_eq_two_mul hn

/-! ## Mersenne Numbers and Primes -/

/-- The Mersenne number Mₚ = 2ᵖ - 1.
    When Mₚ is prime, we call it a Mersenne prime. -/
theorem mersenne_def (p : ℕ) : mersenne p = 2 ^ p - 1 := rfl

/-- Useful identity: σ(2^k) = 2^(k+1) - 1 = M_{k+1}
    The sum of divisors of a power of 2 is the next Mersenne number. -/
theorem sigma_two_pow (k : ℕ) : σ 1 (2 ^ k) = mersenne (k + 1) :=
  Theorems100.Nat.sigma_two_pow_eq_mersenne_succ k

/-! ## Euclid's Theorem: Mersenne Prime → Perfect Number -/

/-- **Euclid's Theorem** (Elements IX.36):
    If 2ᵖ - 1 is prime, then 2ᵖ⁻¹ × (2ᵖ - 1) is perfect.

    For example:
    - p = 2: 2¹ × 3 = 6 is perfect
    - p = 3: 2² × 7 = 28 is perfect
    - p = 5: 2⁴ × 31 = 496 is perfect
    - p = 7: 2⁶ × 127 = 8128 is perfect -/
theorem euclid_perfect_numbers (k : ℕ) (hp : (mersenne (k + 1)).Prime) :
    (2 ^ k * mersenne (k + 1)).Perfect :=
  Theorems100.Nat.perfect_two_pow_mul_mersenne_of_prime k hp

/-! ## Euler's Theorem: Even Perfect → Mersenne Form -/

/-- **Euler's Theorem** (1747):
    Every even perfect number has the form 2^k × (2^(k+1) - 1)
    where 2^(k+1) - 1 is a Mersenne prime.

    This took over 2000 years after Euclid to prove! -/
theorem euler_even_perfect (n : ℕ) (h_even : Even n) (h_perfect : n.Perfect) :
    ∃ k, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1) :=
  Theorems100.Nat.eq_two_pow_mul_prime_mersenne_of_even_perfect h_even h_perfect

/-! ## The Complete Characterization -/

/-- **The Euclid-Euler Theorem**: Complete characterization of even perfect numbers.

    n is even and perfect if and only if n = 2^k × (2^(k+1) - 1) for some k
    where 2^(k+1) - 1 is a Mersenne prime.

    This combines Euclid's ancient result with Euler's 18th century proof. -/
theorem even_perfect_iff (n : ℕ) :
    (Even n ∧ n.Perfect) ↔
    ∃ k, (mersenne (k + 1)).Prime ∧ n = 2 ^ k * mersenne (k + 1) :=
  Theorems100.Nat.even_and_perfect_iff

/-! ## Concrete Examples

We verify the first four perfect numbers, corresponding to the first
four Mersenne primes: 3, 7, 31, 127. -/

/-- 6 is the first perfect number: 6 = 1 + 2 + 3.
    It corresponds to the Mersenne prime M₂ = 3.
    We have 6 = 2¹ × 3 = 2¹ × (2² - 1). -/
theorem six_is_perfect : Nat.Perfect 6 := by
  have h3_prime : (mersenne 2).Prime := by native_decide
  have h := euclid_perfect_numbers 1 h3_prime
  simp only [mersenne, pow_one] at h
  exact h

/-- 28 is the second perfect number: 28 = 1 + 2 + 4 + 7 + 14.
    It corresponds to the Mersenne prime M₃ = 7.
    We have 28 = 2² × 7 = 2² × (2³ - 1). -/
theorem twentyeight_is_perfect : Nat.Perfect 28 := by
  have h7_prime : (mersenne 3).Prime := by native_decide
  have h := euclid_perfect_numbers 2 h7_prime
  simp only [mersenne] at h
  exact h

/-- 496 is the third perfect number.
    It corresponds to the Mersenne prime M₅ = 31.
    We have 496 = 2⁴ × 31 = 2⁴ × (2⁵ - 1). -/
theorem fourhundredninetysix_is_perfect : Nat.Perfect 496 := by
  have h31_prime : (mersenne 5).Prime := by native_decide
  have h := euclid_perfect_numbers 4 h31_prime
  simp only [mersenne] at h
  exact h

/-- 8128 is the fourth perfect number.
    It corresponds to the Mersenne prime M₇ = 127.
    We have 8128 = 2⁶ × 127 = 2⁶ × (2⁷ - 1). -/
theorem eightthousandonetwentyeight_is_perfect : Nat.Perfect 8128 := by
  have h127_prime : (mersenne 7).Prime := by native_decide
  have h := euclid_perfect_numbers 6 h127_prime
  simp only [mersenne] at h
  exact h

/-! ## Why This Matters

The Perfect Number Theorem is remarkable for several reasons:

1. **Ancient + Modern**: Euclid's result is 2300 years old, yet Euler's
   converse required 18th century techniques. Complete characterization
   took over two millennia!

2. **Open Problem**: We still don't know if odd perfect numbers exist!
   This is one of the oldest unsolved problems in mathematics. We know:
   - If one exists, it must be > 10^1500
   - It must have at least 101 prime factors
   - Many other constraints... but no proof either way

3. **Mersenne Primes**: Perfect numbers are intimately tied to Mersenne
   primes. Finding new Mersenne primes (via GIMPS) gives new perfect numbers.
   As of 2024, only 51 Mersenne primes are known.

4. **Multiplicative Functions**: The proof uses σ being multiplicative:
   σ(mn) = σ(m)σ(n) when gcd(m,n) = 1. This is the key algebraic fact. -/

/-! ## The Formula in Action

For n = 2^k × (2^(k+1) - 1) with M = 2^(k+1) - 1 prime:

σ(n) = σ(2^k) × σ(M)           -- σ is multiplicative, gcd = 1
     = (2^(k+1) - 1) × (M + 1)  -- σ(2^k) = M, σ(M) = 1 + M (prime)
     = M × 2^(k+1)
     = 2 × (2^k × M)
     = 2n

So n.Perfect! -/

#check euclid_perfect_numbers
#check euler_even_perfect
#check even_perfect_iff

end PerfectNumbers
