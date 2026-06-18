/-
Divisibility by 7 via k-digit Block Alternating Sums

Since 1000 ≡ -1 (mod 7), a natural number n is divisible by 7 iff the
alternating sum of its 3-digit blocks is divisible by 7.

Example: 1234567 has 3-digit blocks [567, 234, 1] (little-endian in base 1000).
  Alternating sum = 567 - 234 + 1 = 334
  334 = 47 × 7 + 5, so 334 is NOT divisible by 7.
  1234567 = 176366 × 7 + 5, confirming 7 ∤ 1234567.

This generalizes: for any d where b^k ≡ -1 (mod d), we get a divisibility
rule using k-digit block alternating sums.

Key instances:
  - 10 ≡ -1 (mod 11) → alternating digit sum (1-digit blocks)
  - 100 ≡ -1 (mod 101) → alternating 2-digit blocks
  - 1000 ≡ -1 (mod 7) → alternating 3-digit blocks (this file)
  - 1000 ≡ -1 (mod 13) → alternating 3-digit blocks for 13

References:
  - Parent: Proofs.DivisibilityRules (alternatingDigitSum, altDigitSum)
  - Proofs.DivisibilityRulesOQ01 (digit-sum rules via dvd_iff_dvd_digits_sum)
-/

import Proofs.DivisibilityRules

open DivisibilityRules

namespace DivisibilityRulesOQ02

-- ═══════════════════════════════════════════════════════════════
-- PART I: THE KEY CONGRUENCE 1000 ≡ -1 (mod 7)
-- ═══════════════════════════════════════════════════════════════

/-- 1000 ≡ -1 (mod 7), equivalently 1000 % 7 = 6 = 7 - 1.
    This is the foundation of the 3-digit block alternating sum rule. -/
theorem thousand_mod_seven : 1000 % 7 = 6 := by native_decide

-- ═══════════════════════════════════════════════════════════════
-- PART II: DIVISIBILITY BY 7 VIA ALTERNATING 3-DIGIT BLOCKS
-- ═══════════════════════════════════════════════════════════════

/-- **Divisibility by 7 via alternating 3-digit blocks**:
    n ≡ altDigitSum 1000 n (mod 7), where altDigitSum 1000 n computes
    the alternating sum of 3-digit blocks of n.

    Since 1000 ≡ -1 (mod 7), writing n = a₀ + a₁·1000 + a₂·1000² + ...
    gives n ≡ a₀ - a₁ + a₂ - a₃ + ... (mod 7). -/
theorem seven_modEq_altDigitSum_1000 (n : ℕ) :
    (n : ℤ) ≡ altDigitSum 1000 n [ZMOD 7] :=
  modEq_alternating_digits_sum 7 1000 n (by norm_num) thousand_mod_seven

/-- **General alternating block rule**: For any d > 0 and base b with
    b ≡ -1 (mod d), we have d | n iff d | altDigitSum b n.

    This unifies:
    - d=11, b=10: alternating digit sum (1-digit blocks)
    - d=7, b=1000: alternating 3-digit blocks
    - d=13, b=1000: alternating 3-digit blocks
    - d=101, b=100: alternating 2-digit blocks -/
theorem dvd_iff_dvd_altDigitSum (d b n : ℕ) (hd : 0 < d)
    (hb : b % d = d - 1) :
    (d : ℤ) ∣ ↑n ↔ (d : ℤ) ∣ altDigitSum b n := by
  have hmod := modEq_alternating_digits_sum d b n hd hb
  constructor
  · intro h
    have := dvd_add hmod.dvd h
    rwa [sub_add_cancel] at this
  · intro h
    have := dvd_add hmod.symm.dvd h
    rwa [sub_add_cancel] at this

/-- **Divisibility test**: 7 | n iff 7 | alternating sum of 3-digit blocks. -/
theorem seven_dvd_iff_altDigitSum (n : ℕ) :
    (7 : ℤ) ∣ ↑n ↔ (7 : ℤ) ∣ altDigitSum 1000 n :=
  dvd_iff_dvd_altDigitSum 7 1000 n (by norm_num) thousand_mod_seven

-- ═══════════════════════════════════════════════════════════════
-- PART III: DIVISIBILITY BY 13 VIA ALTERNATING 3-DIGIT BLOCKS
-- ═══════════════════════════════════════════════════════════════

/-- 1000 ≡ -1 (mod 13), since 1000 = 76 × 13 + 12 = 76 × 13 + (13-1). -/
theorem thousand_mod_thirteen : 1000 % 13 = 12 := by native_decide

/-- **Divisibility by 13 via alternating 3-digit blocks**:
    n ≡ altDigitSum 1000 n (mod 13). -/
theorem thirteen_modEq_altDigitSum_1000 (n : ℕ) :
    (n : ℤ) ≡ altDigitSum 1000 n [ZMOD 13] :=
  modEq_alternating_digits_sum 13 1000 n (by norm_num) thousand_mod_thirteen

/-- **Divisibility test**: 13 | n iff 13 | alternating sum of 3-digit blocks. -/
theorem thirteen_dvd_iff_altDigitSum (n : ℕ) :
    (13 : ℤ) ∣ ↑n ↔ (13 : ℤ) ∣ altDigitSum 1000 n :=
  dvd_iff_dvd_altDigitSum 13 1000 n (by norm_num) thousand_mod_thirteen

-- ═══════════════════════════════════════════════════════════════
-- PART V: CONCRETE EXAMPLES (VERIFICATION)
-- ═══════════════════════════════════════════════════════════════

/-- 1001 = 143 × 7, so 7 | 1001. Verified via 3-digit blocks:
    blocks of 1001 in base 1000 are [1, 1], alternating sum = 1 - 1 = 0. -/
example : 7 ∣ 1001 := by native_decide

/-- 1234567 is not divisible by 7: 1234567 = 176366 × 7 + 5. -/
example : ¬(7 ∣ 1234567) := by native_decide

/-- 2002 = 286 × 7, so 7 | 2002. Blocks: [2, 2], alt sum = 2 - 2 = 0. -/
example : 7 ∣ 2002 := by native_decide

/-- 91 = 13 × 7, so both 7 | 91 and 13 | 91. -/
example : 7 ∣ 91 ∧ 13 ∣ 91 := ⟨⟨13, by norm_num⟩, ⟨7, by norm_num⟩⟩

/-- **Divisibility by 11 via single digits** (classical rule).
    10 ≡ -1 (mod 11), so alternating digit sum works. -/
theorem eleven_dvd_iff_altDigitSum (n : ℕ) :
    (11 : ℤ) ∣ ↑n ↔ (11 : ℤ) ∣ altDigitSum 10 n :=
  dvd_iff_dvd_altDigitSum 11 10 n (by norm_num) (by native_decide)

/-- **Divisibility by 101 via alternating 2-digit blocks**.
    100 ≡ -1 (mod 101). -/
theorem hundredone_dvd_iff_altDigitSum (n : ℕ) :
    (101 : ℤ) ∣ ↑n ↔ (101 : ℤ) ∣ altDigitSum 100 n :=
  dvd_iff_dvd_altDigitSum 101 100 n (by norm_num) (by native_decide)

/-!
## Summary

**Proved (0 sorries; concrete instances depend on Lean.ofReduceBool via native_decide):**
1. **seven_modEq_altDigitSum_1000**: n ≡ altDigitSum₁₀₀₀(n) (mod 7)
2. **seven_dvd_iff_altDigitSum**: 7 | n ↔ 7 | altDigitSum₁₀₀₀(n)
3. **thirteen_modEq_altDigitSum_1000**: n ≡ altDigitSum₁₀₀₀(n) (mod 13)
4. **thirteen_dvd_iff_altDigitSum**: 13 | n ↔ 13 | altDigitSum₁₀₀₀(n)
5. **dvd_iff_dvd_altDigitSum**: General alternating block rule
6. **eleven_dvd_iff_altDigitSum**: Classical div-by-11 as instance
7. **hundredone_dvd_iff_altDigitSum**: Div-by-101 via 2-digit blocks

**Key insight**: 1000 ≡ -1 (mod 7) and 1000 ≡ -1 (mod 13), so the
3-digit block alternating sum gives divisibility rules for both 7 and 13.
-/

end DivisibilityRulesOQ02
