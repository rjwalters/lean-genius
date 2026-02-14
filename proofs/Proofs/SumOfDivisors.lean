/-
# Sum of Divisors Function: Properties and Classification

## What This Proves

The sum of divisors function σ(n) = Σ_{d|n} d is one of the most studied
functions in number theory. This file formalizes key properties of σ including:

1. **Basic values**: σ(n) for many small n
2. **Primes**: σ(p) = p + 1 verified for specific primes
3. **Bounds**: σ(n) > n verified for small n
4. **Classification**: Deficient, perfect, and abundant numbers
5. **Amicable pairs**: (220, 284) and (1184, 1210)

## Approach
- **Foundation**: Mathlib's `ArithmeticFunction.sigma` provides the σ function
- **Proof techniques**: `native_decide` for concrete verified computations,
  omega for arithmetic reasoning

## Status
- [x] Concrete σ values (13 values verified)
- [x] σ(p) = p + 1 for specific primes (6 primes verified)
- [x] Number classification with examples (11 classifications)
- [x] Amicable pair verification (2 pairs)
- [x] Divisor count function d(n) (6 values)
- [x] Higher-order σ₂ values (3 values)
- [x] Classification theory (exhaustive + exclusive)
- [x] Abundancy index characterization
- [x] General bounds: σ(n) ≥ n for n ≥ 1, σ(n) > n for n > 1
- [x] σ(p) = p + 1 for all primes (general theorem)
- [x] σ is multiplicative (structural theorem)
- [x] σ(p^k) = Σ p^i for prime p (general prime power formula)
- [x] Factorization-based computation of σ
- [x] 12 is the smallest abundant number (minimality proof)

## Mathlib Dependencies
- `ArithmeticFunction.sigma` : Sum of divisors function
- `Nat.divisors` : Divisor set
-/

import Mathlib

namespace SumOfDivisors

open Nat ArithmeticFunction Finset

/-
## Part 1: Concrete σ Values

The function σ(n) = Σ_{d|n} d sums all positive divisors.
We verify σ for many small values using decidability.
-/

/-- σ(1) = 1: The only divisor of 1 is 1 itself. -/
theorem sigma_one_eq : sigma 1 1 = 1 := by native_decide

/-- σ(2) = 3: Divisors of 2 are {1, 2}, sum = 3. -/
theorem sigma_two_eq : sigma 1 2 = 3 := by native_decide

/-- σ(3) = 4: Divisors of 3 are {1, 3}, sum = 4. -/
theorem sigma_three_eq : sigma 1 3 = 4 := by native_decide

/-- σ(4) = 7: Divisors of 4 are {1, 2, 4}, sum = 7. -/
theorem sigma_four_eq : sigma 1 4 = 7 := by native_decide

/-- σ(5) = 6: Divisors of 5 are {1, 5}, sum = 6. -/
theorem sigma_five_eq : sigma 1 5 = 6 := by native_decide

/-- σ(6) = 12: Divisors of 6 are {1, 2, 3, 6}, sum = 12. -/
theorem sigma_six_eq : sigma 1 6 = 12 := by native_decide

/-- σ(7) = 8: Divisors of 7 are {1, 7}, sum = 8. -/
theorem sigma_seven_eq : sigma 1 7 = 8 := by native_decide

/-- σ(8) = 15: Divisors of 8 are {1, 2, 4, 8}, sum = 15. -/
theorem sigma_eight_eq : sigma 1 8 = 15 := by native_decide

/-- σ(9) = 13: Divisors of 9 are {1, 3, 9}, sum = 13. -/
theorem sigma_nine_eq : sigma 1 9 = 13 := by native_decide

/-- σ(10) = 18: Divisors of 10 are {1, 2, 5, 10}, sum = 18. -/
theorem sigma_ten_eq : sigma 1 10 = 18 := by native_decide

/-- σ(12) = 28: Divisors of 12 are {1, 2, 3, 4, 6, 12}, sum = 28. -/
theorem sigma_twelve_eq : sigma 1 12 = 28 := by native_decide

/-- σ(28) = 56: 28 is a perfect number, so σ(28) = 2 × 28. -/
theorem sigma_twentyeight_eq : sigma 1 28 = 56 := by native_decide

/-- σ(100) = 217. -/
theorem sigma_hundred_eq : sigma 1 100 = 217 := by native_decide

/-
## Part 2: σ on Primes

For any prime p, the only divisors are 1 and p, so σ(p) = p + 1.
We verify this for specific primes via native_decide.
-/

/-- σ(2) = 2 + 1 = 3. The smallest prime. -/
theorem sigma_prime_2 : sigma 1 2 = 2 + 1 := by native_decide

/-- σ(3) = 3 + 1 = 4. -/
theorem sigma_prime_3 : sigma 1 3 = 3 + 1 := by native_decide

/-- σ(5) = 5 + 1 = 6. -/
theorem sigma_prime_5 : sigma 1 5 = 5 + 1 := by native_decide

/-- σ(7) = 7 + 1 = 8. -/
theorem sigma_prime_7 : sigma 1 7 = 7 + 1 := by native_decide

/-- σ(11) = 11 + 1 = 12. -/
theorem sigma_prime_11 : sigma 1 11 = 11 + 1 := by native_decide

/-- σ(13) = 13 + 1 = 14. -/
theorem sigma_prime_13 : sigma 1 13 = 13 + 1 := by native_decide

/-- σ(p) = p + 1 for prime p: primes have exactly two divisors. -/
theorem sigma_prime (p : ℕ) (hp : p.Prime) : sigma 1 p = p + 1 := by
  have h : sigma 1 (p ^ 1) = ∑ j ∈ Finset.range 2, p ^ (j * 1) :=
    sigma_apply_prime_pow hp
  simp [pow_one, Finset.sum_range_succ] at h
  linarith

/-
## Part 3: Number Classification

Every positive integer falls into exactly one of three categories
based on how σ(n) compares with 2n:

- **Deficient**: σ(n) < 2n (most numbers)
- **Perfect**: σ(n) = 2n (extremely rare: 6, 28, 496, 8128, ...)
- **Abundant**: σ(n) > 2n (first example: 12)
-/

/-- A number is deficient if σ(n) < 2n. -/
def IsDeficient (n : ℕ) : Prop := sigma 1 n < 2 * n

/-- A number is perfect if σ(n) = 2n. -/
def IsPerfect (n : ℕ) : Prop := sigma 1 n = 2 * n

/-- A number is abundant if σ(n) > 2n. -/
def IsAbundant (n : ℕ) : Prop := sigma 1 n > 2 * n

/-- Every prime p ≥ 2 is deficient: σ(p) = p + 1 < 2p. -/
theorem prime_is_deficient (p : ℕ) (hp : p.Prime) : IsDeficient p := by
  unfold IsDeficient
  have h := sigma_prime p hp
  have := hp.two_le
  omega

/-- 1 is deficient: σ(1) = 1 < 2. -/
theorem one_is_deficient : IsDeficient 1 := by
  unfold IsDeficient; native_decide

/-- 2 is deficient: σ(2) = 3 < 4. -/
theorem two_is_deficient : IsDeficient 2 := by
  unfold IsDeficient; native_decide

/-- 4 is deficient: σ(4) = 7 < 8. -/
theorem four_is_deficient : IsDeficient 4 := by
  unfold IsDeficient; native_decide

/-- 8 is deficient: σ(8) = 15 < 16. -/
theorem eight_is_deficient : IsDeficient 8 := by
  unfold IsDeficient; native_decide

/-- 6 is perfect: σ(6) = 12 = 2 × 6. The first perfect number (known to Euclid). -/
theorem six_is_perfect : IsPerfect 6 := by
  unfold IsPerfect; native_decide

/-- 28 is perfect: σ(28) = 56 = 2 × 28. The second perfect number. -/
theorem twentyeight_is_perfect : IsPerfect 28 := by
  unfold IsPerfect; native_decide

/-- 496 is perfect: the third perfect number. -/
theorem fourhundredninetysix_is_perfect : IsPerfect 496 := by
  unfold IsPerfect; native_decide

/-- 12 is the first abundant number: σ(12) = 28 > 24 = 2 × 12. -/
theorem twelve_is_abundant : IsAbundant 12 := by
  unfold IsAbundant; native_decide

/-- 18 is abundant: σ(18) = 39 > 36. -/
theorem eighteen_is_abundant : IsAbundant 18 := by
  unfold IsAbundant; native_decide

/-- 20 is abundant: σ(20) = 42 > 40. -/
theorem twenty_is_abundant : IsAbundant 20 := by
  unfold IsAbundant; native_decide

/-- 24 is abundant: σ(24) = 60 > 48. -/
theorem twentyfour_is_abundant : IsAbundant 24 := by
  unfold IsAbundant; native_decide

/-
## Part 4: Classification Theory

The three categories are exhaustive and mutually exclusive.
-/

/-- Classification is exhaustive: every n is deficient, perfect, or abundant. -/
theorem classification_exhaustive (n : ℕ) :
    IsDeficient n ∨ IsPerfect n ∨ IsAbundant n := by
  unfold IsDeficient IsPerfect IsAbundant; omega

/-- Deficient and perfect are exclusive. -/
theorem deficient_not_perfect (n : ℕ) (h : IsDeficient n) : ¬IsPerfect n := by
  unfold IsDeficient IsPerfect at *; omega

/-- Deficient and abundant are exclusive. -/
theorem deficient_not_abundant (n : ℕ) (h : IsDeficient n) : ¬IsAbundant n := by
  unfold IsDeficient IsAbundant at *; omega

/-- Perfect and abundant are exclusive. -/
theorem perfect_not_abundant (n : ℕ) (h : IsPerfect n) : ¬IsAbundant n := by
  unfold IsPerfect IsAbundant at *; omega

/-
## Part 5: Amicable Numbers

Two numbers m and n are *amicable* if s(m) = n and s(n) = m,
where s(k) = σ(k) - k is the sum of proper divisors.

The pair (220, 284) is the smallest amicable pair, known to the Pythagoreans (~300 BCE).
-/

/-- Two numbers are amicable if each equals the sum of proper divisors of the other. -/
def AreAmicable (m n : ℕ) : Prop :=
  m ≠ n ∧ sigma 1 m - m = n ∧ sigma 1 n - n = m

/-- σ(220) = 504. -/
theorem sigma_220 : sigma 1 220 = 504 := by native_decide

/-- σ(284) = 504. -/
theorem sigma_284 : sigma 1 284 = 504 := by native_decide

/-- 220 and 284 form an amicable pair (known to the Pythagoreans).
    s(220) = σ(220) - 220 = 504 - 220 = 284
    s(284) = σ(284) - 284 = 504 - 284 = 220 -/
theorem amicable_220_284 : AreAmicable 220 284 := by
  unfold AreAmicable
  refine ⟨by omega, ?_, ?_⟩
  · have h := sigma_220; omega
  · have h := sigma_284; omega

/-- σ(1184) = 2394. -/
theorem sigma_1184 : sigma 1 1184 = 2394 := by native_decide

/-- σ(1210) = 2394. -/
theorem sigma_1210 : sigma 1 1210 = 2394 := by native_decide

/-- 1184 and 1210 form the second-smallest amicable pair
    (discovered by 16-year-old Niccolò Paganini in 1866). -/
theorem amicable_1184_1210 : AreAmicable 1184 1210 := by
  unfold AreAmicable
  refine ⟨by omega, ?_, ?_⟩
  · have h := sigma_1184; omega
  · have h := sigma_1210; omega

/-
## Part 6: The Abundancy Index

The *abundancy index* of n is σ(n)/n. This measures how "divisor-rich" n is.
- Deficient: abundancy < 2
- Perfect: abundancy = 2
- Abundant: abundancy > 2
-/

/-- The abundancy index σ(n)/n as a rational number. -/
noncomputable def abundancy (n : ℕ) : ℚ :=
  (sigma 1 n : ℚ) / (n : ℚ)

/-- n is perfect iff abundancy = 2 (for n > 0). -/
theorem perfect_iff_abundancy_two (n : ℕ) (hn : 0 < n) :
    IsPerfect n ↔ abundancy n = 2 := by
  unfold IsPerfect abundancy
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  constructor
  · intro h
    field_simp
    push_cast [h]
    ring
  · intro h
    rw [div_eq_iff hn'] at h
    have h' : (sigma 1 n : ℤ) = 2 * (n : ℤ) := by exact_mod_cast h
    omega

/-
## Part 7: Divisor Count Function

The zeroth-order divisor sum σ_0(n) = d(n) counts the number of divisors.
-/

/-- d(1) = 1. -/
theorem divisor_count_one : sigma 0 1 = 1 := by native_decide

/-- d(2) = 2: divisors are {1, 2}. -/
theorem divisor_count_two : sigma 0 2 = 2 := by native_decide

/-- d(4) = 3: divisors of 4 = 2² are {1, 2, 4}. -/
theorem divisor_count_four : sigma 0 4 = 3 := by native_decide

/-- d(6) = 4: divisors are {1, 2, 3, 6}. -/
theorem divisor_count_six : sigma 0 6 = 4 := by native_decide

/-- d(12) = 6: divisors are {1, 2, 3, 4, 6, 12}. -/
theorem divisor_count_twelve : sigma 0 12 = 6 := by native_decide

/-- d(2^10) = 11: powers of 2 have d(2^k) = k + 1. -/
theorem divisor_count_1024 : sigma 0 1024 = 11 := by native_decide

/-
## Part 8: σ₂ (Sum of Squares of Divisors)

The second-order divisor sum σ₂(n) = Σ_{d|n} d².
-/

/-- σ₂(1) = 1. -/
theorem sigma2_one : sigma 2 1 = 1 := by native_decide

/-- σ₂(2) = 1² + 2² = 5. -/
theorem sigma2_two : sigma 2 2 = 5 := by native_decide

/-- σ₂(6) = 1² + 2² + 3² + 6² = 1 + 4 + 9 + 36 = 50. -/
theorem sigma2_six : sigma 2 6 = 50 := by native_decide

/-
## Part 9: Key Bounds

The sum of divisors satisfies σ(n) > n for n > 1 (since 1 and n are both divisors).
We verify bounds for specific values.
-/

/-- σ(n) ≥ n for small n: verified computationally. -/
theorem sigma_ge_2 : sigma 1 2 ≥ 2 := by native_decide
theorem sigma_ge_3 : sigma 1 3 ≥ 3 := by native_decide
theorem sigma_ge_6 : sigma 1 6 ≥ 6 := by native_decide
theorem sigma_ge_10 : sigma 1 10 ≥ 10 := by native_decide
theorem sigma_ge_100 : sigma 1 100 ≥ 100 := by native_decide

/-- σ(n) > n for n > 1: verified computationally. -/
theorem sigma_gt_2 : sigma 1 2 > 2 := by native_decide
theorem sigma_gt_3 : sigma 1 3 > 3 := by native_decide
theorem sigma_gt_10 : sigma 1 10 > 10 := by native_decide
theorem sigma_gt_100 : sigma 1 100 > 100 := by native_decide

/-- σ(n) ≥ n for all n ≥ 1. -/
theorem sigma_ge_self (n : ℕ) (hn : 0 < n) : sigma 1 n ≥ n := by
  have hmem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, hn.ne'⟩
  have heval : (fun d => d ^ 1) n = n := by ring
  calc sigma 1 n = ∑ d ∈ n.divisors, d ^ 1 := by simp [sigma_apply]
    _ ≥ n ^ 1 := Finset.single_le_sum (fun d _ => Nat.zero_le _) hmem
    _ = n := by ring

/-- For n > 1: σ(n) > n. -/
theorem sigma_gt_self (n : ℕ) (hn : n > 1) : sigma 1 n > n := by
  have h1mem : 1 ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n, (by omega : n ≠ 0)⟩
  have hnmem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl n, (by omega : n ≠ 0)⟩
  have hne : (1 : ℕ) ≠ n := by omega
  have hsub : {1, n} ⊆ n.divisors := by
    intro d hd; simp at hd; rcases hd with rfl | rfl <;> assumption
  calc sigma 1 n = ∑ d ∈ n.divisors, d ^ 1 := by simp [sigma_apply]
    _ ≥ ∑ d ∈ ({1, n} : Finset ℕ), d ^ 1 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => Nat.zero_le _)
    _ = 1 ^ 1 + n ^ 1 := by rw [Finset.sum_pair hne]
    _ = 1 + n := by ring
    _ > n := by omega

/-
## Part 10: Connections to Other Areas

### Robin's Inequality (Equivalent to RH)
σ(n) < e^γ · n · ln(ln(n)) for n ≥ 5041, iff the Riemann Hypothesis holds.

### Gronwall's Theorem
lim sup_{n → ∞} σ(n)/(n · ln(ln(n))) = e^γ ≈ 1.7811

### Ramanujan's Highly Composite Numbers
Numbers n where d(n) > d(m) for all m < n.
First few: 1, 2, 4, 6, 12, 24, 36, 48, 60, 120, ...

These connections motivate further study of σ properties.
-/

/-
## Part 11: Multiplicativity of σ

The sum of divisors function is *multiplicative*: σ(mn) = σ(m)σ(n) whenever
gcd(m,n) = 1. This is the key algebraic property that makes σ computable from
the prime factorization.
-/

/-- σ_k is a multiplicative arithmetic function. -/
theorem sigma_multiplicative (k : ℕ) : ArithmeticFunction.IsMultiplicative (sigma k) :=
  isMultiplicative_sigma

/-- σ(1) = 1, from multiplicativity. -/
theorem sigma_one_from_mult : sigma 1 1 = 1 :=
  isMultiplicative_sigma.map_one

/-- Multiplicativity: σ(mn) = σ(m) · σ(n) when gcd(m,n) = 1. -/
theorem sigma_mul_coprime (m n : ℕ) (h : Nat.Coprime m n) :
    sigma 1 (m * n) = sigma 1 m * sigma 1 n :=
  isMultiplicative_sigma.map_mul_of_coprime h

/-- Example: σ(6) = σ(2) · σ(3) since gcd(2,3) = 1. -/
theorem sigma_six_mult : sigma 1 (2 * 3) = sigma 1 2 * sigma 1 3 :=
  sigma_mul_coprime 2 3 (by native_decide)

/-- Example: σ(12) = σ(4) · σ(3) since gcd(4,3) = 1.
    This gives 28 = 7 × 4, verified. -/
theorem sigma_twelve_mult : sigma 1 (4 * 3) = sigma 1 4 * sigma 1 3 :=
  sigma_mul_coprime 4 3 (by native_decide)

/-- Example: σ(30) = σ(2) · σ(15) = σ(2) · σ(3) · σ(5). -/
theorem sigma_thirty_mult : sigma 1 (2 * 15) = sigma 1 2 * sigma 1 15 :=
  sigma_mul_coprime 2 15 (by native_decide)

/-
## Part 12: σ on Prime Powers

For prime p, the divisors of p^k are exactly {1, p, p², ..., p^k}.
Therefore σ(p^k) = 1 + p + p² + ... + p^k = Σ_{i=0}^k p^i.

This is the formula that, combined with multiplicativity, lets us compute
σ(n) from the prime factorization of n.
-/

/-- σ(p^k) = Σ_{i=0}^k p^i for prime p.
    This is the fundamental formula for σ on prime powers. -/
theorem sigma_prime_pow (p k : ℕ) (hp : p.Prime) :
    sigma 1 (p ^ k) = ∑ i ∈ Finset.range (k + 1), p ^ i := by
  rw [sigma_apply_prime_pow hp]
  congr 1; ext i; ring

/-- σ(p) = 1 + p for prime p (special case k=1). -/
theorem sigma_prime_pow_one (p : ℕ) (hp : p.Prime) :
    sigma 1 (p ^ 1) = 1 + p := by
  rw [sigma_prime_pow p 1 hp]
  simp [Finset.sum_range_succ]

/-- σ(p²) = 1 + p + p² for prime p. -/
theorem sigma_prime_pow_two (p : ℕ) (hp : p.Prime) :
    sigma 1 (p ^ 2) = 1 + p + p ^ 2 := by
  rw [sigma_prime_pow p 2 hp]
  simp [Finset.sum_range_succ]

/-- σ(p³) = 1 + p + p² + p³ for prime p. -/
theorem sigma_prime_pow_three (p : ℕ) (hp : p.Prime) :
    sigma 1 (p ^ 3) = 1 + p + p ^ 2 + p ^ 3 := by
  rw [sigma_prime_pow p 3 hp]
  simp [Finset.sum_range_succ]

/-- Concrete verification: σ(4) = σ(2²) = 1 + 2 + 4 = 7. -/
theorem sigma_four_via_formula : sigma 1 (2 ^ 2) = 1 + 2 + 2 ^ 2 :=
  sigma_prime_pow_two 2 (by norm_num)

/-- Concrete verification: σ(8) = σ(2³) = 1 + 2 + 4 + 8 = 15. -/
theorem sigma_eight_via_formula : sigma 1 (2 ^ 3) = 1 + 2 + 2 ^ 2 + 2 ^ 3 :=
  sigma_prime_pow_three 2 (by norm_num)

/-- Concrete verification: σ(9) = σ(3²) = 1 + 3 + 9 = 13. -/
theorem sigma_nine_via_formula : sigma 1 (3 ^ 2) = 1 + 3 + 3 ^ 2 :=
  sigma_prime_pow_two 3 (by norm_num)

/-- Concrete verification: σ(27) = σ(3³) = 1 + 3 + 9 + 27 = 40. -/
theorem sigma_twentyseven_via_formula : sigma 1 (3 ^ 3) = 1 + 3 + 3 ^ 2 + 3 ^ 3 :=
  sigma_prime_pow_three 3 (by norm_num)

/-
## Part 13: Computing σ via Factorization

Combining multiplicativity with the prime power formula:
  σ(p₁^a₁ · p₂^a₂ · ... · pₖ^aₖ) = σ(p₁^a₁) · σ(p₂^a₂) · ... · σ(pₖ^aₖ)
  = (Σ p₁^i) · (Σ p₂^j) · ...

Example: σ(12) = σ(2² · 3) = σ(4) · σ(3) = 7 · 4 = 28.
-/

/-- σ(12) computed via factorization: 12 = 2² · 3, so
    σ(12) = σ(4) · σ(3) = (1+2+4)(1+3) = 7·4 = 28. -/
theorem sigma_twelve_via_factorization :
    sigma 1 12 = (1 + 2 + 2^2) * (1 + 3) := by
  have h12 : (12 : ℕ) = 2^2 * 3 := by norm_num
  have hcop : Nat.Coprime (2^2) 3 := by native_decide
  have h4 := sigma_prime_pow_two 2 (by norm_num)
  have h3 := sigma_prime 3 (by norm_num)
  rw [h12, sigma_mul_coprime _ _ hcop, h4]
  simp [h3]

/-- σ(30) computed via factorization: 30 = 2 · 3 · 5, so
    σ(30) = σ(2) · σ(3) · σ(5) = 3 · 4 · 6 = 72. -/
theorem sigma_thirty_via_factorization :
    sigma 1 30 = (1 + 2) * (1 + 3) * (1 + 5) := by
  have h30 : (30 : ℕ) = 2 * (3 * 5) := by norm_num
  have hcop1 : Nat.Coprime 2 (3 * 5) := by native_decide
  have hcop2 : Nat.Coprime 3 5 := by native_decide
  rw [h30, sigma_mul_coprime _ _ hcop1, sigma_mul_coprime _ _ hcop2]
  have h2 := sigma_prime 2 (by norm_num)
  have h3 := sigma_prime 3 (by norm_num)
  have h5 := sigma_prime 5 (by norm_num)
  rw [h2, h3, h5]

/-
## Part 14: Smallest Abundant Number

12 is the first abundant number. We prove this by showing every n < 12 is
not abundant (i.e., σ(n) ≤ 2n).
-/

/-- No number from 1 to 11 is abundant. -/
theorem not_abundant_lt_12 (n : ℕ) (hn1 : 0 < n) (hn2 : n < 12) :
    ¬IsAbundant n := by
  unfold IsAbundant
  interval_cases n <;> simp_all <;> native_decide

/-- 12 is the smallest abundant number. -/
theorem twelve_smallest_abundant :
    IsAbundant 12 ∧ ∀ n, 0 < n → n < 12 → ¬IsAbundant n :=
  ⟨twelve_is_abundant, not_abundant_lt_12⟩

/-
## Summary

This file formalizes key properties of the sum of divisors function:

**Proven (no sorry)**:
- σ concrete values: σ(1) through σ(10), σ(12), σ(28), σ(100),
  σ(220), σ(284), σ(1184), σ(1210) — 17 verified values
- σ(p) = p + 1 verified for p = 2, 3, 5, 7, 11, 13 and general theorem
- Number classification: 1,2,4,8 deficient; 6,28,496 perfect; 12,18,20,24 abundant
- All primes are deficient (σ(p) = p + 1 < 2p)
- Classification exhaustive and exclusive (4 theorems)
- Amicable pairs: (220, 284) and (1184, 1210) — fully verified
- d(n) concrete values: d(1)=1, d(2)=2, d(4)=3, d(6)=4, d(12)=6, d(1024)=11
- σ₂ concrete values: σ₂(1)=1, σ₂(2)=5, σ₂(6)=50
- σ(n) ≥ n for n ≥ 1 (general) and σ(n) > n for n > 1 (general)
- Perfect iff abundancy = 2
- σ is multiplicative: σ(mn) = σ(m)·σ(n) for coprime m,n
- σ(p^k) = Σ_{i=0}^k p^i for prime p (general formula)
- σ on prime powers: specialized for k=1,2,3
- Factorization examples: σ(12) and σ(30) via factorization
- 12 is the smallest abundant number (proved minimality)

**Total: ~85 declarations, 0 sorries, 0 axioms**
-/

end SumOfDivisors
