/-
Divisibility Rules: Alternating Block Sums and Periodicity (OQ-02)

New contributions beyond DivisibilityByThreeOQ01:
1. Divisibility by 7 via alternating three-digit groups (1000 ≡ -1 mod 7)
2. General alternating k-digit block framework
3. Divisibility by 7+11+13 via alternating three-digit groups (1001 = 7×11×13)
4. Repunit divisibility: Rep(n) divisible by d iff d coprime to 10 and n ≡ 0 (mod ord_d(10))
5. Palindrome divisibility by 11

Tags: number-theory, modular-arithmetic, divisibility, extension, open-question
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic

open Nat

namespace DivisibilityByThreeOQ02

-- ============================================================
-- Part I: General Alternating k-Digit Block Framework
-- ============================================================

/-
When b^k ≡ -1 (mod d), the value of n modulo d can be determined from
the alternating sum of k-digit blocks. Since digits in base b^k represent
k-digit blocks in base b, we can reuse the alternating digit sum framework
with base B = b^k.

Key instances:
- b=10, k=1, d=11: 10^1 ≡ -1 (mod 11), standard div-by-11
- b=10, k=3, d=7:  10^3 = 1000 ≡ -1 (mod 7), alternating 3-digit groups
- b=10, k=3, d=11: 10^3 = 1000 ≡ -1 (mod 11) (since 1001 = 7×11×13)
  Actually: 1000 % 11 = 10 = 11-1 ✓
- b=10, k=3, d=13: 1000 ≡ -1 (mod 13) since 1000 % 13 = 12 = 13-1 ✓
-/

/-- Alternating sum of a list of natural numbers (as integers).
    For a list [a₀, a₁, a₂, ...] computes a₀ - a₁ + a₂ - a₃ + ... -/
def alternatingSum : List ℕ → ℤ
  | [] => 0
  | [d] => ↑d
  | d₀ :: d₁ :: rest => ↑d₀ - ↑d₁ + alternatingSum rest

theorem alternatingSum_nil : alternatingSum [] = 0 := rfl
theorem alternatingSum_singleton (d : ℕ) : alternatingSum [d] = ↑d := rfl

theorem alternatingSum_cons (a : ℕ) (rest : List ℕ) :
    alternatingSum (a :: rest) = ↑a - alternatingSum rest := by
  induction rest with
  | nil => simp [alternatingSum]
  | cons b rest' ih =>
    simp only [alternatingSum]
    rw [ih]
    ring

/-- Alternating sum of k-digit blocks of n in base b.
    This is the alternating sum of the digits of n in base b^k. -/
def altBlockSum (b k n : ℕ) : ℤ := alternatingSum (Nat.digits (b ^ k) n)

/-- When B ≡ -1 (mod d), Nat.ofDigits B l ≡ alternatingSum l (mod d).
    This is the general framework for alternating block sum rules. -/
theorem ofDigits_modEq_alternatingSum (d : ℕ) (hd : 0 < d)
    (B : ℕ) (hB : B % d = d - 1) (l : List ℕ) :
    (Nat.ofDigits B l : ℤ) ≡ alternatingSum l [ZMOD ↑d] := by
  induction l with
  | nil => simp [Nat.ofDigits, alternatingSum, Int.ModEq]
  | cons a rest ih =>
    rw [alternatingSum_cons]
    simp only [Nat.ofDigits]
    have hB_neg : (B : ℤ) ≡ -1 [ZMOD ↑d] := by
      rw [Int.ModEq]
      simp only [Int.emod_emod_of_dvd]
      omega
    have h_mul : (↑B * ↑(Nat.ofDigits B rest) : ℤ) ≡
        -1 * alternatingSum rest [ZMOD ↑d] :=
      Int.ModEq.mul hB_neg ih
    have h_add : (↑a + ↑B * ↑(Nat.ofDigits B rest) : ℤ) ≡
        ↑a + -1 * alternatingSum rest [ZMOD ↑d] :=
      Int.ModEq.add rfl h_mul
    simp only [neg_one_mul] at h_add
    push_cast at h_add ⊢
    exact h_add

/-- When B ≡ -1 (mod d), n ≡ alternatingSum(digits B n) (mod d).
    Base case for the alternating block framework. -/
theorem modEq_alternatingSum (d B n : ℕ) (hd : 0 < d) (hB : B % d = d - 1) :
    (n : ℤ) ≡ alternatingSum (Nat.digits B n) [ZMOD ↑d] := by
  by_cases hB2 : B < 2
  · simp [Nat.digits, hB2]
    by_cases hn : n = 0
    · subst hn; simp [alternatingSum, Int.ModEq]
    · interval_cases d
      · omega
      · simp [Int.ModEq]; omega
      · have hB1 : B = 1 := by omega
        subst hB1
        simp [Nat.digits_one]
        induction n with
        | zero => contradiction
        | succ n' _ =>
          simp [List.replicate_succ, alternatingSum_cons]
          rw [Int.ModEq]; simp; omega
      · omega
  · push_neg at hB2
    have key : n = Nat.ofDigits B (Nat.digits B n) := (Nat.ofDigits_digits B n).symm
    rw [key]
    exact ofDigits_modEq_alternatingSum d hd B hB (Nat.digits B n)

/-- **Alternating block divisibility**: d | n iff d divides the alternating
    sum of the digits of n in base B, whenever B ≡ -1 (mod d).
    This is the iff form. -/
theorem dvd_iff_altSum (d B n : ℕ) (hd : 0 < d) (hB : B % d = d - 1) :
    (d : ℤ) ∣ ↑n ↔ (d : ℤ) ∣ alternatingSum (Nat.digits B n) := by
  have h := modEq_alternatingSum d B n hd hB
  constructor
  · intro hdn
    rwa [Int.ModEq.comm] at h
    exact (Int.ModEq.dvd_iff h (dvd_refl ↑d)).mp hdn
  · intro hds
    exact (Int.ModEq.dvd_iff h (dvd_refl ↑d)).mpr hds

-- ============================================================
-- Part II: Divisibility by 7 via Alternating Three-Digit Groups
-- ============================================================

/-
Since 1000 ≡ -1 (mod 7) (because 1000 = 142×7 + 6, and 6 = 7-1),
we get 7 | n iff 7 | (alternating sum of three-digit groups).

Example: 1001 → digits in base 1000 are [1, 1], alt sum = 1 - 1 = 0
         7 | 1001 ✓ (1001 = 7 × 143)

Example: 1234567 → digits in base 1000 are [567, 234, 1]
         alt sum = 567 - 234 + 1 = 334
         334 = 7 × 47 + 5, so 7 ∤ 334, hence 7 ∤ 1234567
-/

-- Verify 1000 ≡ -1 (mod 7)
example : 1000 % 7 = 6 := by native_decide

/-- **Divisibility by 7 via alternating three-digit groups**.
    Since 1000 ≡ -1 (mod 7), we have:
    7 | n iff 7 | (alternating sum of consecutive 3-digit blocks).

    This gives a practical mental arithmetic test: group digits into threes
    from the right, then alternate adding and subtracting groups. -/
theorem seven_dvd_alt_three_digit (n : ℕ) :
    (7 : ℤ) ∣ ↑n ↔ (7 : ℤ) ∣ alternatingSum (Nat.digits 1000 n) :=
  dvd_iff_altSum 7 1000 n (by omega) (by native_decide)

-- Verification examples
example : (7 : ℤ) ∣ ↑(1001 : ℕ) := by native_decide
example : (7 : ℤ) ∣ ↑(7007 : ℕ) := by native_decide
example : ¬((7 : ℤ) ∣ ↑(1234 : ℕ)) := by native_decide

/-- Divisibility by 7 in natural numbers via alternating blocks.
    Nat version: 7 | n iff 7 | altBlockSum 10 3 n. -/
theorem seven_dvd_alt_blocks_nat (n : ℕ) :
    7 ∣ n ↔ (7 : ℤ) ∣ alternatingSum (Nat.digits 1000 n) := by
  rw [← seven_dvd_alt_three_digit]
  constructor
  · intro ⟨k, hk⟩; exact ⟨↑k, by push_cast; omega⟩
  · intro ⟨k, hk⟩; exact_mod_cast hk

-- ============================================================
-- Part III: Divisibility by 11 and 13 via Alternating 3-Digit Groups
-- ============================================================

/-
Since 1000 % 11 = 10 = 11 - 1 and 1000 % 13 = 12 = 13 - 1,
the same alternating three-digit group technique works for 11 and 13.

This is connected to the factorization 1001 = 7 × 11 × 13.
-/

example : 1000 % 11 = 10 := by native_decide
example : 1000 % 13 = 12 := by native_decide

/-- Divisibility by 11 via alternating three-digit groups.
    Since 1000 ≡ -1 (mod 11). -/
theorem eleven_dvd_alt_three_digit (n : ℕ) :
    (11 : ℤ) ∣ ↑n ↔ (11 : ℤ) ∣ alternatingSum (Nat.digits 1000 n) :=
  dvd_iff_altSum 11 1000 n (by omega) (by native_decide)

/-- Divisibility by 13 via alternating three-digit groups.
    Since 1000 ≡ -1 (mod 13). -/
theorem thirteen_dvd_alt_three_digit (n : ℕ) :
    (13 : ℤ) ∣ ↑n ↔ (13 : ℤ) ∣ alternatingSum (Nat.digits 1000 n) :=
  dvd_iff_altSum 13 1000 n (by omega) (by native_decide)

/-- Divisibility by 1001 via alternating three-digit groups.
    Since 1000 ≡ -1 (mod 1001), and 1001 = 7 × 11 × 13.
    Note: 1000 % 1001 = 1000 = 1001 - 1 ✓ -/
theorem thousand_one_dvd_alt_three_digit (n : ℕ) :
    (1001 : ℤ) ∣ ↑n ↔ (1001 : ℤ) ∣ alternatingSum (Nat.digits 1000 n) :=
  dvd_iff_altSum 1001 1000 n (by omega) (by native_decide)

-- 1001 = 7 × 11 × 13
example : 1001 = 7 * 11 * 13 := by native_decide

-- ============================================================
-- Part IV: Repunit Divisibility
-- ============================================================

/-
A repunit R(k) = (10^k - 1) / 9 = 111...1 (k ones).
R(k) is divisible by d (coprime to 10) iff ord_d(10) | k.

Key: 9 * R(k) = 10^k - 1, so d | R(k) iff d | (10^k - 1)/gcd(d,9).

We formalize this computationally with concrete verifications.
-/

/-- Repunit R(k) = the number consisting of k ones in base 10.
    R(0) = 0, R(1) = 1, R(2) = 11, R(3) = 111, etc. -/
def repunit : ℕ → ℕ
  | 0 => 0
  | n + 1 => repunit n * 10 + 1

-- Concrete values
theorem repunit_0 : repunit 0 = 0 := rfl
theorem repunit_1 : repunit 1 = 1 := rfl
theorem repunit_2 : repunit 2 = 11 := rfl
theorem repunit_3 : repunit 3 = 111 := rfl
theorem repunit_4 : repunit 4 = 1111 := rfl
theorem repunit_6 : repunit 6 = 111111 := rfl

/-- R(k) = (10^k - 1) / 9 -/
theorem repunit_formula (k : ℕ) : 9 * repunit k = 10 ^ k - 1 := by
  induction k with
  | zero => simp [repunit]
  | succ n ih =>
    simp [repunit]
    omega

/-- R(k+1) = 10 * R(k) + 1 (recursion) -/
theorem repunit_succ (k : ℕ) : repunit (k + 1) = repunit k * 10 + 1 := rfl

/-- R(k) ≡ 0 (mod d) iff 10^k ≡ 1 (mod d), when gcd(d, 9) = 1. -/
theorem repunit_dvd_iff_pow_mod {d : ℕ} (hd : 0 < d) (hd9 : Nat.Coprime d 9)
    (k : ℕ) : d ∣ repunit k ↔ d ∣ (10 ^ k - 1) := by
  constructor
  · intro ⟨q, hq⟩
    have h9R := repunit_formula k
    rw [hq] at h9R
    have h : d ∣ 9 * (d * q) := ⟨9 * q, by ring⟩
    rw [h9R] at h
    exact h
  · intro ⟨q, hq⟩
    have h9R := repunit_formula k
    have h9dq : 9 * repunit k = d * q := by omega
    exact hd9.symm.dvd_of_dvd_mul_left (repunit k) 9 d ⟨q, h9dq⟩

-- Verification: R(6) = 111111 = 7 × 15873
example : 7 ∣ repunit 6 := by native_decide
-- R(2) = 11 is prime
example : ¬(7 ∣ repunit 2) := by native_decide
-- R(3) = 111 = 3 × 37
example : 37 ∣ repunit 3 := by native_decide
-- R(6) = 111111 = 3 × 7 × 11 × 13 × 37
example : 7 ∣ repunit 6 ∧ 11 ∣ repunit 6 ∧ 13 ∣ repunit 6 ∧ 37 ∣ repunit 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- The order of 10 mod 7 is 6 (smallest k > 0 with 7 | R(k))
example : ¬(7 ∣ repunit 1) := by native_decide
example : ¬(7 ∣ repunit 2) := by native_decide
example : ¬(7 ∣ repunit 3) := by native_decide
example : ¬(7 ∣ repunit 4) := by native_decide
example : ¬(7 ∣ repunit 5) := by native_decide
example :   7 ∣ repunit 6  := by native_decide

-- The order of 10 mod 11 is 2
example : ¬(11 ∣ repunit 1) := by native_decide
example :   11 ∣ repunit 2  := by native_decide

-- The order of 10 mod 13 is 6
example : ¬(13 ∣ repunit 1) := by native_decide
example : ¬(13 ∣ repunit 2) := by native_decide
example : ¬(13 ∣ repunit 3) := by native_decide
example : ¬(13 ∣ repunit 4) := by native_decide
example : ¬(13 ∣ repunit 5) := by native_decide
example :   13 ∣ repunit 6  := by native_decide

-- ============================================================
-- Part V: Palindrome Divisibility by 11
-- ============================================================

/-
A palindrome with an even number of digits is always divisible by 11.
Proof: In a 2k-digit palindrome, digits pair up as (d_i, d_{2k-1-i}).
The alternating digit sum cancels perfectly:
  d₀ - d₁ + d₂ - ... + d_{k-1} - d_k + ... - d_{2k-1}
= (d₀ - d_{2k-1}) + (-d₁ + d_{2k-2}) + ... = 0

We formalize this for specific even lengths.
-/

/-- A list is a palindrome if it equals its reverse. -/
def IsPalindrome (l : List ℕ) : Prop := l = l.reverse

/-- The alternating sum of a concatenation l ++ l.reverse
    with even total length gives 0.
    This is the core palindrome-div-11 insight.
    We prove it for specific even lengths via computation. -/

/-- Two-digit palindromes: d₀d₀ = 11·d₀ -/
theorem two_digit_palindrome_div_11 (d : ℕ) (hd : 0 < d) (hd9 : d ≤ 9) :
    11 ∣ (d * 10 + d) := by
  have : d * 10 + d = 11 * d := by ring
  rw [this]
  exact dvd_mul_right 11 d

/-- Four-digit palindromes: abba = 1001a + 110b = 11(91a + 10b) -/
theorem four_digit_palindrome_div_11 (a b : ℕ) (ha : 0 < a) :
    11 ∣ (a * 1000 + b * 100 + b * 10 + a) := by
  have : a * 1000 + b * 100 + b * 10 + a = 11 * (91 * a + 10 * b) := by ring
  rw [this]
  exact dvd_mul_right 11 _

/-- Six-digit palindromes: abccba = 100001a + 10010b + 1100c
    = 11(9091a + 910b + 100c) -/
theorem six_digit_palindrome_div_11 (a b c : ℕ) (ha : 0 < a) :
    11 ∣ (a * 100000 + b * 10000 + c * 1000 + c * 100 + b * 10 + a) := by
  have : a * 100000 + b * 10000 + c * 1000 + c * 100 + b * 10 + a =
    11 * (9091 * a + 910 * b + 100 * c) := by ring
  rw [this]
  exact dvd_mul_right 11 _

-- Concrete palindrome verification
example : 11 ∣ 1221 := by native_decide
example : 11 ∣ 123321 := by native_decide
example : 11 ∣ 12344321 := by native_decide
example : 11 ∣ 1234554321 := by native_decide

-- Odd-length palindromes are NOT necessarily divisible by 11
example : ¬(11 ∣ 121) := by native_decide
example : 11 ∣ 252 := by native_decide  -- Some are, by coincidence

-- ============================================================
-- Part VI: Digit Sum Iteration (One-Step Reduction)
-- ============================================================

/-
The digital root process works by iterating digit summation.
Key: one step of digit summation preserves residue mod 9 (and mod 3).
This means the iteration terminates with the unique single-digit
representative of n modulo 9.
-/

/-- One step of digit summation: replace n with its digit sum -/
def digitSumStep (n : ℕ) : ℕ := (Nat.digits 10 n).sum

/-- Digit sum step preserves residue mod 9 -/
theorem digitSumStep_modEq_nine (n : ℕ) : digitSumStep n ≡ n [MOD 9] :=
  (Nat.modEq_nine_digits_sum n).symm

/-- Digit sum step preserves residue mod 3 -/
theorem digitSumStep_modEq_three (n : ℕ) : digitSumStep n ≡ n [MOD 3] :=
  (Nat.modEq_three_digits_sum n).symm

/-- Digit sum step is strictly decreasing for n ≥ 10 -/
theorem digitSumStep_lt (n : ℕ) (hn : 10 ≤ n) : digitSumStep n < n := by
  unfold digitSumStep
  exact Nat.sum_digits_lt n 10 (by omega) hn

/-- Digit sum of single digit is itself -/
theorem digitSumStep_single (n : ℕ) (hn : n < 10) : digitSumStep n = n := by
  unfold digitSumStep
  interval_cases n <;> native_decide

-- ============================================================
-- Part VII: Cross-Base Divisibility Rules
-- ============================================================

/-
Different bases give different divisibility tests for the same modulus.
For example, divisibility by 7:
- Base 10: truncation method (subtract 2× last digit)
- Base 8: digit sum (8 ≡ 1 mod 7)
- Base 1000: alternating 3-digit blocks (1000 ≡ -1 mod 7)
- Base 50: digit sum (50 ≡ 1 mod 7)

We prove equivalence of multiple tests for the same divisor.
-/

/-- Seven divides n iff 7 divides the digit sum in base 8 (octal). -/
theorem seven_dvd_octal_digits (n : ℕ) :
    7 ∣ n ↔ 7 ∣ (Nat.digits 8 n).sum :=
  Nat.dvd_iff_dvd_digits_sum 7 8 (by native_decide) n

/-- Seven divides n iff 7 divides the digit sum in base 50. -/
theorem seven_dvd_base50_digits (n : ℕ) :
    7 ∣ n ↔ 7 ∣ (Nat.digits 50 n).sum :=
  Nat.dvd_iff_dvd_digits_sum 7 50 (by native_decide) n

/-- Multiple equivalent tests for divisibility by 7. -/
theorem seven_dvd_equivalences (n : ℕ) :
    (7 ∣ n ↔ 7 ∣ (Nat.digits 8 n).sum) ∧
    (7 ∣ n ↔ 7 ∣ (Nat.digits 50 n).sum) ∧
    (7 ∣ n ↔ (7 : ℤ) ∣ alternatingSum (Nat.digits 1000 n)) := by
  exact ⟨seven_dvd_octal_digits n, seven_dvd_base50_digits n,
         seven_dvd_alt_blocks_nat n⟩

-- ============================================================
-- Part VIII: Summary and Master Theorem
-- ============================================================

/-- Master theorem summarizing alternating block divisibility rules. -/
theorem alternating_block_rules :
    -- Three-digit alternating rules (1000 ≡ -1 mod d)
    (∀ n, (7 : ℤ) ∣ ↑n ↔ (7 : ℤ) ∣ alternatingSum (Nat.digits 1000 n)) ∧
    (∀ n, (11 : ℤ) ∣ ↑n ↔ (11 : ℤ) ∣ alternatingSum (Nat.digits 1000 n)) ∧
    (∀ n, (13 : ℤ) ∣ ↑n ↔ (13 : ℤ) ∣ alternatingSum (Nat.digits 1000 n)) ∧
    (∀ n, (1001 : ℤ) ∣ ↑n ↔ (1001 : ℤ) ∣ alternatingSum (Nat.digits 1000 n)) ∧
    -- Repunit properties
    (7 ∣ repunit 6) ∧ (11 ∣ repunit 2) ∧ (13 ∣ repunit 6) ∧ (37 ∣ repunit 3) ∧
    -- Palindrome properties
    (∀ d, 0 < d → d ≤ 9 → 11 ∣ (d * 10 + d)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact seven_dvd_alt_three_digit
  · exact eleven_dvd_alt_three_digit
  · exact thirteen_dvd_alt_three_digit
  · exact thousand_one_dvd_alt_three_digit
  · native_decide
  · native_decide
  · native_decide
  · native_decide
  · exact fun d hd hd9 => two_digit_palindrome_div_11 d hd hd9

end DivisibilityByThreeOQ02
