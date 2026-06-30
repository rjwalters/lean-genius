/-
General Truncation Divisibility Rule (Open Question: divisibility-by-3-oq-01-oq-01)
Date: 2026-02-21
Research: divisibility-by-3-oq-01-oq-01

Answers the question: "Can the truncation method be generalized to a single
parametric theorem for all divisors coprime to 10?"

YES. We prove two general theorems covering all cases:

1. **Positive osculator** (10c ≡ 1 mod d):
   d | n ↔ d | (n/10 + c·(n%10))
   Examples: d=13 c=4, d=19 c=2, d=3 c=10 (but c=1 also works for 3)

2. **Negative osculator** (10c ≡ -1 mod d, i.e., 10c + 1 ≡ 0 mod d):
   d | n ↔ d | (n/10 - c·(n%10))
   Examples: d=7 c=2, d=11 c=1, d=17 c=5

Together, these subsume ALL specific truncation rules. The proof follows
a clean algebraic pattern:

  10·(n/10 + c·(n%10)) = n + (10c - 1)·(n%10)

When d | (10c - 1), and gcd(d, 10) = 1, divisibility transfers.
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic

open Nat

namespace DivisibilityTruncationGeneral

/-
## The Core Lemma: Division/Modulus Identity in ℤ
-/

/-- n = 10·(n/10) + n%10, cast to ℤ -/
private lemma div_mod_cast (n : ℕ) : (n : ℤ) = 10 * ↑(n / 10) + ↑(n % 10) := by
  have := Nat.div_add_mod n 10
  push_cast
  omega

/-
## The General Positive Osculator Theorem
-/

/-- **General Truncation Rule (Positive Osculator)**

    For any divisor d coprime to 10 with positive osculator c
    (satisfying d | 10c - 1, equivalently 10c ≡ 1 mod d):

      d | n  ↔  d | (n/10 + c·(n%10))

    This gives a "remove last digit and add c times it" divisibility test.

    Key examples (using c as integer for unified positive/negative case):
    - d=13, c=4:  10·4=40, 40-1=39=3·13 ✓  → 13 | n ↔ 13 | (n/10 + 4·(n%10))
    - d=19, c=2:  10·2=20, 20-1=19=1·19 ✓  → 19 | n ↔ 19 | (n/10 + 2·(n%10))
    - d=3,  c=1:  10·1=10, 10-1=9=3·3 ✓    → 3  | n ↔ 3  | (n/10 + 1·(n%10))

    Note: For negative osculator cases, use the variant theorem below,
    or equivalently use negative c here with d | (10c - 1). -/
theorem truncation_pos (d : ℕ) (c : ℤ) (n : ℕ)
    (hcop : IsCoprime (d : ℤ) 10)
    (hc : (d : ℤ) ∣ 10 * c - 1) :
    (d : ℤ) ∣ n ↔ (d : ℤ) ∣ (↑(n / 10) + c * ↑(n % 10)) := by
  have hdiv := div_mod_cast n
  have hkey : (10 : ℤ) * (↑(n / 10) + c * ↑(n % 10)) = ↑n + (10 * c - 1) * ↑(n % 10) := by
    linear_combination -hdiv
  constructor
  · intro hn
    have h1 : (d : ℤ) ∣ ↑n + (10 * c - 1) * ↑(n % 10) :=
      dvd_add hn (dvd_mul_of_dvd_left hc _)
    rw [← hkey] at h1
    exact hcop.dvd_of_dvd_mul_left h1
  · intro hq
    have h10 : (d : ℤ) ∣ 10 * (↑(n / 10) + c * ↑(n % 10)) :=
      dvd_mul_of_dvd_right hq 10
    rw [hkey] at h10
    have hterm : (d : ℤ) ∣ (10 * c - 1) * ↑(n % 10) := dvd_mul_of_dvd_left hc _
    have hsub := Int.dvd_sub h10 hterm
    simp only [add_sub_cancel_right] at hsub
    exact_mod_cast hsub

/-
## The General Negative Osculator Theorem
-/

/-- **General Truncation Rule (Negative Osculator)**

    For any divisor d coprime to 10 with negative osculator c
    (satisfying d | 10c + 1, equivalently 10c ≡ -1 mod d):

      d | n  ↔  d | (n/10 - c·(n%10))

    This gives a "remove last digit and subtract c times it" divisibility test.

    Key examples:
    - d=7,  c=2:  10·2=20, 20+1=21=3·7 ✓   → 7  | n ↔ 7  | (n/10 - 2·(n%10))
    - d=11, c=1:  10·1=10, 10+1=11=1·11 ✓  → 11 | n ↔ 11 | (n/10 - 1·(n%10))
    - d=17, c=5:  10·5=50, 50+1=51=3·17 ✓  → 17 | n ↔ 17 | (n/10 - 5·(n%10)) -/
theorem truncation_neg (d : ℕ) (c : ℤ) (n : ℕ)
    (hcop : IsCoprime (d : ℤ) 10)
    (hc : (d : ℤ) ∣ 10 * c + 1) :
    (d : ℤ) ∣ n ↔ (d : ℤ) ∣ (↑(n / 10) - c * ↑(n % 10)) := by
  have hdiv := div_mod_cast n
  have hkey : (10 : ℤ) * (↑(n / 10) - c * ↑(n % 10)) = ↑n - (10 * c + 1) * ↑(n % 10) := by
    linear_combination -hdiv
  constructor
  · intro hn
    have h1 : (d : ℤ) ∣ ↑n - (10 * c + 1) * ↑(n % 10) :=
      Int.dvd_sub hn (dvd_mul_of_dvd_left hc _)
    rw [← hkey] at h1
    exact hcop.dvd_of_dvd_mul_left h1
  · intro hq
    have h10 : (d : ℤ) ∣ 10 * (↑(n / 10) - c * ↑(n % 10)) :=
      dvd_mul_of_dvd_right hq 10
    rw [hkey] at h10
    have hterm : (d : ℤ) ∣ (10 * c + 1) * ↑(n % 10) := dvd_mul_of_dvd_left hc _
    have hadd := Int.dvd_add h10 hterm
    simp only [sub_add_cancel] at hadd
    exact_mod_cast hadd

/-
## Verification: Recovering All Specific Cases
-/

/-- d=7, negative osculator c=2: 10·2+1 = 21 = 3·7 -/
theorem seven_dvd_trunc (n : ℕ) :
    (7 : ℤ) ∣ n ↔ (7 : ℤ) ∣ (↑(n / 10) - 2 * ↑(n % 10)) :=
  truncation_neg 7 2 n (by decide) ⟨3, by norm_num⟩

/-- d=11, negative osculator c=1: 10·1+1 = 11 = 1·11 -/
theorem eleven_dvd_trunc (n : ℕ) :
    (11 : ℤ) ∣ n ↔ (11 : ℤ) ∣ (↑(n / 10) - 1 * ↑(n % 10)) :=
  truncation_neg 11 1 n (by decide) ⟨1, by norm_num⟩

/-- d=13, positive osculator c=4: 10·4-1 = 39 = 3·13 -/
theorem thirteen_dvd_trunc (n : ℕ) :
    (13 : ℤ) ∣ n ↔ (13 : ℤ) ∣ (↑(n / 10) + 4 * ↑(n % 10)) :=
  truncation_pos 13 4 n (by decide) ⟨3, by norm_num⟩

/-- d=17, negative osculator c=5: 10·5+1 = 51 = 3·17 -/
theorem seventeen_dvd_trunc (n : ℕ) :
    (17 : ℤ) ∣ n ↔ (17 : ℤ) ∣ (↑(n / 10) - 5 * ↑(n % 10)) :=
  truncation_neg 17 5 n (by decide) ⟨3, by norm_num⟩

/-- d=19, positive osculator c=2: 10·2-1 = 19 = 1·19 -/
theorem nineteen_dvd_trunc (n : ℕ) :
    (19 : ℤ) ∣ n ↔ (19 : ℤ) ∣ (↑(n / 10) + 2 * ↑(n % 10)) :=
  truncation_pos 19 2 n (by decide) ⟨1, by norm_num⟩

/-- d=3, positive osculator c=1: 10·1-1 = 9 = 3·3 -/
theorem three_dvd_trunc (n : ℕ) :
    (3 : ℤ) ∣ n ↔ (3 : ℤ) ∣ (↑(n / 10) + 1 * ↑(n % 10)) :=
  truncation_pos 3 1 n (by decide) ⟨3, by norm_num⟩

/-- d=9, positive osculator c=1: 10·1-1 = 9 = 1·9 -/
theorem nine_dvd_trunc (n : ℕ) :
    (9 : ℤ) ∣ n ↔ (9 : ℤ) ∣ (↑(n / 10) + 1 * ↑(n % 10)) :=
  truncation_pos 9 1 n (by decide) ⟨1, by norm_num⟩

/-- d=23, positive osculator c=7: 10·7-1 = 69 = 3·23 -/
theorem twentythree_dvd_trunc (n : ℕ) :
    (23 : ℤ) ∣ n ↔ (23 : ℤ) ∣ (↑(n / 10) + 7 * ↑(n % 10)) :=
  truncation_pos 23 7 n (by decide) ⟨3, by norm_num⟩

/-- d=29, positive osculator c=3: 10·3-1 = 29 = 1·29 -/
theorem twentynine_dvd_trunc (n : ℕ) :
    (29 : ℤ) ∣ n ↔ (29 : ℤ) ∣ (↑(n / 10) + 3 * ↑(n % 10)) :=
  truncation_pos 29 3 n (by decide) ⟨1, by norm_num⟩

/-- d=31, negative osculator c=3: 10·3+1 = 31 = 1·31 -/
theorem thirtyone_dvd_trunc (n : ℕ) :
    (31 : ℤ) ∣ n ↔ (31 : ℤ) ∣ (↑(n / 10) - 3 * ↑(n % 10)) :=
  truncation_neg 31 3 n (by decide) ⟨1, by norm_num⟩

/-- d=37, negative osculator c=11: 10·11+1 = 111 = 3·37 -/
theorem thirtyseven_dvd_trunc (n : ℕ) :
    (37 : ℤ) ∣ n ↔ (37 : ℤ) ∣ (↑(n / 10) - 11 * ↑(n % 10)) :=
  truncation_neg 37 11 n (by decide) ⟨3, by norm_num⟩

/-- d=41, negative osculator c=4: 10·4+1 = 41 = 1·41 -/
theorem fortyone_dvd_trunc (n : ℕ) :
    (41 : ℤ) ∣ n ↔ (41 : ℤ) ∣ (↑(n / 10) - 4 * ↑(n % 10)) :=
  truncation_neg 41 4 n (by decide) ⟨1, by norm_num⟩

/-- d=43, positive osculator c=13: 10·13-1 = 129 = 3·43 -/
theorem fortythree_dvd_trunc (n : ℕ) :
    (43 : ℤ) ∣ n ↔ (43 : ℤ) ∣ (↑(n / 10) + 13 * ↑(n % 10)) :=
  truncation_pos 43 13 n (by decide) ⟨3, by norm_num⟩

/-
## Osculator Table
-/

/-- Verification of key osculator relationships -/
-- Positive osculators (10c - 1 ≡ 0 mod d):
example : (13 : ℤ) ∣ 10 * 4 - 1 := ⟨3, by norm_num⟩   -- 39 = 3 × 13
example : (19 : ℤ) ∣ 10 * 2 - 1 := ⟨1, by norm_num⟩   -- 19 = 1 × 19
example : (3 : ℤ) ∣ 10 * 1 - 1 := ⟨3, by norm_num⟩    -- 9 = 3 × 3
example : (9 : ℤ) ∣ 10 * 1 - 1 := ⟨1, by norm_num⟩    -- 9 = 1 × 9
example : (23 : ℤ) ∣ 10 * 7 - 1 := ⟨3, by norm_num⟩   -- 69 = 3 × 23
example : (29 : ℤ) ∣ 10 * 3 - 1 := ⟨1, by norm_num⟩   -- 29 = 1 × 29
example : (43 : ℤ) ∣ 10 * 13 - 1 := ⟨3, by norm_num⟩  -- 129 = 3 × 43

-- Negative osculators (10c + 1 ≡ 0 mod d):
example : (7 : ℤ) ∣ 10 * 2 + 1 := ⟨3, by norm_num⟩    -- 21 = 3 × 7
example : (11 : ℤ) ∣ 10 * 1 + 1 := ⟨1, by norm_num⟩   -- 11 = 1 × 11
example : (17 : ℤ) ∣ 10 * 5 + 1 := ⟨3, by norm_num⟩   -- 51 = 3 × 17
example : (31 : ℤ) ∣ 10 * 3 + 1 := ⟨1, by norm_num⟩   -- 31 = 1 × 31
example : (37 : ℤ) ∣ 10 * 11 + 1 := ⟨3, by norm_num⟩  -- 111 = 3 × 37
example : (41 : ℤ) ∣ 10 * 4 + 1 := ⟨1, by norm_num⟩   -- 41 = 1 × 41

/-
## Examples and Sanity Checks
-/

-- 7 | 49: 49 → 4 - 2·9 = 4 - 18 = -14, 7 | -14 ✓
example : 7 ∣ 49 := by native_decide
example : (7 : ℤ) ∣ (4 : ℤ) - 2 * 9 := ⟨-2, by norm_num⟩

-- 13 | 169: 169 → 16 + 4·9 = 16 + 36 = 52, 13 | 52 ✓
example : 13 ∣ 169 := by native_decide
example : (13 : ℤ) ∣ (16 : ℤ) + 4 * 9 := ⟨4, by norm_num⟩

-- 19 | 57: 57 → 5 + 2·7 = 5 + 14 = 19, 19 | 19 ✓
example : 19 ∣ 57 := by native_decide
example : (19 : ℤ) ∣ (5 : ℤ) + 2 * 7 := ⟨1, by norm_num⟩

-- 17 | 51: 51 → 5 - 5·1 = 0, 17 | 0 ✓
example : 17 ∣ 51 := by native_decide
example : (17 : ℤ) ∣ (5 : ℤ) - 5 * 1 := ⟨0, by norm_num⟩

/-
## Summary Theorem: The General Method Works
-/

/-- **Main Result**: The truncation method generalizes to a single parametric theorem.

    For ANY d coprime to 10, EITHER a positive osculator c exists (d | 10c - 1)
    giving rule  d | n ↔ d | (n/10 + c·(n%10)),
    OR a negative osculator c exists (d | 10c + 1)
    giving rule  d | n ↔ d | (n/10 - c·(n%10)).

    Since gcd(d, 10) = 1 iff d coprime to 10, there always exists a
    multiplicative inverse of 10 mod d. The positive osculator is that inverse
    (10⁻¹ mod d), with c = 10⁻¹ mod d.
    The negative osculator uses c = -(10⁻¹) mod d = d - 10⁻¹.

    This gives a UNIFORM characterization of ALL truncation-based divisibility rules. -/
theorem truncation_method_summary :
    -- Seven: negative osculator 2
    (∀ n : ℕ, (7 : ℤ) ∣ n ↔ (7 : ℤ) ∣ (↑(n / 10) - 2 * ↑(n % 10))) ∧
    -- Eleven: negative osculator 1
    (∀ n : ℕ, (11 : ℤ) ∣ n ↔ (11 : ℤ) ∣ (↑(n / 10) - 1 * ↑(n % 10))) ∧
    -- Thirteen: positive osculator 4
    (∀ n : ℕ, (13 : ℤ) ∣ n ↔ (13 : ℤ) ∣ (↑(n / 10) + 4 * ↑(n % 10))) ∧
    -- Seventeen: negative osculator 5
    (∀ n : ℕ, (17 : ℤ) ∣ n ↔ (17 : ℤ) ∣ (↑(n / 10) - 5 * ↑(n % 10))) ∧
    -- Nineteen: positive osculator 2
    (∀ n : ℕ, (19 : ℤ) ∣ n ↔ (19 : ℤ) ∣ (↑(n / 10) + 2 * ↑(n % 10))) :=
  ⟨seven_dvd_trunc, eleven_dvd_trunc, thirteen_dvd_trunc,
   seventeen_dvd_trunc, nineteen_dvd_trunc⟩

/-- **Extended Coverage (osculators beyond 19)**: bundles the truncation rules for
    the next primes coprime to 10 — 23, 29, 31, 37, 41, 43 — each obtained as a direct
    instance of the parametric `truncation_pos` / `truncation_neg` theorems.

    This answers the follow-up question "extend truncation coverage beyond 19
    (23, 29, 31, 37, 41, 43)": every listed prime is covered, with no new machinery
    required — only its osculator constant. -/
theorem extended_truncation_coverage :
    (∀ n : ℕ, (23 : ℤ) ∣ n ↔ (23 : ℤ) ∣ (↑(n / 10) + 7 * ↑(n % 10))) ∧
    (∀ n : ℕ, (29 : ℤ) ∣ n ↔ (29 : ℤ) ∣ (↑(n / 10) + 3 * ↑(n % 10))) ∧
    (∀ n : ℕ, (31 : ℤ) ∣ n ↔ (31 : ℤ) ∣ (↑(n / 10) - 3 * ↑(n % 10))) ∧
    (∀ n : ℕ, (37 : ℤ) ∣ n ↔ (37 : ℤ) ∣ (↑(n / 10) - 11 * ↑(n % 10))) ∧
    (∀ n : ℕ, (41 : ℤ) ∣ n ↔ (41 : ℤ) ∣ (↑(n / 10) - 4 * ↑(n % 10))) ∧
    (∀ n : ℕ, (43 : ℤ) ∣ n ↔ (43 : ℤ) ∣ (↑(n / 10) + 13 * ↑(n % 10))) :=
  ⟨twentythree_dvd_trunc, twentynine_dvd_trunc, thirtyone_dvd_trunc,
   thirtyseven_dvd_trunc, fortyone_dvd_trunc, fortythree_dvd_trunc⟩

end DivisibilityTruncationGeneral
