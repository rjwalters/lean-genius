/-
# Combined Divisibility Test for Divisors Sharing Factors with 10

Open Question (from divisibility-truncation-general-oq-01):
  Can the Unified Osculator Theorem be extended to divisors that *share* factors
  with 10 (e.g. 6, 12, 14, 15, 35) by combining it with the last-`k`-digits
  framework?

The Unified Osculator Theorem (`UnifiedOsculator.unified_osculator`) requires the
divisor to be coprime to 10, so it cannot test divisibility by numbers like 6 or
14 on its own. The last-`k`-digits rules (`DivisibilityRules.four_dvd_iff`,
`eight_dvd_iff`, ...) handle exactly the `2^a · 5^b` part. This file shows the two
frameworks compose, via coprime factorization (CRT), into a **single general
test for every positive divisor**.

Answer: YES. Write `d = s · m` with `s ∣ 10^k` (the part built from 2's and 5's)
and `m` coprime to 10 (with osculator `c`, i.e. `m ∣ 10c - 1`), and `s, m` coprime.
Then

  d ∣ n  ↔  (s ∣ n % 10^k)  ∧  (m ∣ n/10 + c·(n%10))

— the left conjunct is the last-`k`-digits rule, the right conjunct is the
osculator rule. This subsumes the gallery's ad-hoc cases 6, 12, 15, 18, 30 and
covers genuinely new ones such as 14 = 2·7 and 35 = 5·7.
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic
import Proofs.DivisibilityRules
import Proofs.DivisibilityTruncationGeneralOQ01

open Nat
open DivisibilityRules (coprime_mul_dvd_iff)
open UnifiedOsculator (unified_osculator)

namespace CombinedDivisibility

-- ============================================================================
-- Part I: The last-`k`-digits rule for any divisor of a power of ten
-- ============================================================================

/-- **Last-`k`-digits rule (general form).**

    If `s` divides `10^k`, then `s ∣ n` depends only on the last `k` decimal
    digits of `n`, i.e. on `n % 10^k`. This generalises `four_dvd_iff` (s=4,k=2),
    `eight_dvd_iff` (s=8,k=3), `twentyfive_dvd_iff` (s=25,k=2), etc., to an
    arbitrary divisor of a power of ten. -/
theorem dvd_iff_dvd_last_k (s k n : ℕ) (hs : s ∣ 10 ^ k) :
    s ∣ n ↔ s ∣ n % 10 ^ k := by
  have h1 : s ∣ 10 ^ k * (n / 10 ^ k) := hs.mul_right _
  constructor
  · intro hn
    have h2 : s ∣ 10 ^ k * (n / 10 ^ k) + n % 10 ^ k := by
      rw [Nat.div_add_mod]; exact hn
    have hsub := Nat.dvd_sub' h2 h1
    have heq : 10 ^ k * (n / 10 ^ k) + n % 10 ^ k - 10 ^ k * (n / 10 ^ k)
        = n % 10 ^ k := by omega
    rwa [heq] at hsub
  · intro hr
    have h2 : s ∣ 10 ^ k * (n / 10 ^ k) + n % 10 ^ k := dvd_add h1 hr
    rwa [Nat.div_add_mod] at h2

-- ============================================================================
-- Part II: The Combined Divisibility Theorem
-- ============================================================================

/-- **Combined Divisibility Theorem.**

    Let `d = s · m` where
    * `s ∣ 10^k`            (the part of `d` built from factors 2 and 5),
    * `m` is coprime to 10  (with signed osculator `c`, so `m ∣ 10c - 1`),
    * `s` and `m` are coprime.

    Then `d ∣ n` holds iff *both* component tests pass:

      d ∣ n  ↔  (s ∣ n % 10^k)  ∧  (m ∣ n/10 + c·(n%10)).

    The first conjunct is the last-`k`-digits rule (`dvd_iff_dvd_last_k`); the
    second is the Unified Osculator Theorem applied to the coprime part. This is
    the answer to the open question: the osculator and last-digit frameworks
    combine to test divisibility by *any* positive integer. -/
theorem combined_divisibility (s m : ℕ) (c : ℤ) (k n : ℕ)
    (hs : s ∣ 10 ^ k)
    (hcop_sm : Nat.Coprime s m)
    (hmcop : IsCoprime (m : ℤ) 10)
    (hc : (m : ℤ) ∣ 10 * c - 1) :
    s * m ∣ n ↔
      (s ∣ n % 10 ^ k ∧ (m : ℤ) ∣ (↑(n / 10) + c * ↑(n % 10))) := by
  rw [coprime_mul_dvd_iff s m n hcop_sm]
  have bridge : (m ∣ n) ↔ ((m : ℤ) ∣ (n : ℤ)) := by
    constructor <;> intro h <;> exact_mod_cast h
  exact and_congr (dvd_iff_dvd_last_k s k n hs)
    (bridge.trans (unified_osculator m c n hmcop hc))

-- ============================================================================
-- Part III: New concrete rules for divisors sharing factors with 10
-- ============================================================================

/-- **6 = 2·3** : `6 ∣ n ↔ (2 ∣ last digit) ∧ (3 ∣ n/10 + (n%10))`.
    Here `s = 2 ∣ 10^1` and the coprime part `m = 3` has osculator `c = 1`. -/
theorem six_combined (n : ℕ) :
    (2 * 3 : ℕ) ∣ n ↔
      (2 ∣ n % 10 ^ 1 ∧ (3 : ℤ) ∣ (↑(n / 10) + 1 * ↑(n % 10))) :=
  combined_divisibility 2 3 1 1 n (by norm_num) (by decide)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) (by norm_num)

/-- **14 = 2·7** : `14 ∣ n ↔ (2 ∣ last digit) ∧ (7 ∣ n/10 + 5·(n%10))`.
    A genuinely new rule: 14 shares the factor 2 with 10 and has coprime part 7
    with osculator `c = 5` (since `7 ∣ 10·5 - 1 = 49`). -/
theorem fourteen_combined (n : ℕ) :
    (2 * 7 : ℕ) ∣ n ↔
      (2 ∣ n % 10 ^ 1 ∧ (7 : ℤ) ∣ (↑(n / 10) + 5 * ↑(n % 10))) :=
  combined_divisibility 2 7 5 1 n (by norm_num) (by decide)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) (by norm_num)

/-- **12 = 4·3** : uses the last-*two*-digits rule for the 2-part (`4 ∣ 10^2`).
    `12 ∣ n ↔ (4 ∣ n%100) ∧ (3 ∣ n/10 + (n%10))`. -/
theorem twelve_combined (n : ℕ) :
    (4 * 3 : ℕ) ∣ n ↔
      (4 ∣ n % 10 ^ 2 ∧ (3 : ℤ) ∣ (↑(n / 10) + 1 * ↑(n % 10))) :=
  combined_divisibility 4 3 1 2 n (by norm_num) (by decide)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) (by norm_num)

/-- **35 = 5·7** : `35 ∣ n ↔ (5 ∣ last digit) ∧ (7 ∣ n/10 + 5·(n%10))`.
    Another new rule: 35 shares the factor 5 with 10, coprime part 7. -/
theorem thirtyfive_combined (n : ℕ) :
    (5 * 7 : ℕ) ∣ n ↔
      (5 ∣ n % 10 ^ 1 ∧ (7 : ℤ) ∣ (↑(n / 10) + 5 * ↑(n % 10))) :=
  combined_divisibility 5 7 5 1 n (by norm_num) (by decide)
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) (by norm_num)

-- ============================================================================
-- Part IV: Sanity checks (computational ground truth)
-- ============================================================================

example : (6 : ℕ) ∣ 144 := by native_decide
example : ¬ (6 : ℕ) ∣ 145 := by native_decide
example : (14 : ℕ) ∣ 154 := by native_decide
example : ¬ (14 : ℕ) ∣ 160 := by native_decide
example : (35 : ℕ) ∣ 245 := by native_decide
example : (12 : ℕ) ∣ 1452 := by native_decide

#check @combined_divisibility
#check @dvd_iff_dvd_last_k
#check fourteen_combined
#check thirtyfive_combined

end CombinedDivisibility
