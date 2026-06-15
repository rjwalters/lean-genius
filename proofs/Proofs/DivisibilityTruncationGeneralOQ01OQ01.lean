/-
# Combined Osculator Test for Divisors Sharing Factors with 10

Open Question (from `divisibility-truncation-general-oq-01`):
  Can the osculator divisibility test be extended to divisors `d` that *share*
  factors with 10 (e.g. d = 2, 4, 8, 5, 25, 6, 12, 14, ...) by combining it with
  the "last-k-digits" framework?

Answer: **YES**, via the Chinese Remainder Theorem.

Write `d = D · m` where:
  * `D` collects the 2- and 5-parts of `d`, so `D ∣ 10^k` for `k = max v₂(d) v₅(d)`;
  * `m` is coprime to 10 (`gcd(m, 10) = 1`), the osculator-testable part.

Since `gcd(D, m) = 1`, CRT gives `d ∣ n ↔ D ∣ n ∧ m ∣ n`. The first conjunct is
decided by the last `k` digits (`D ∣ n ↔ D ∣ n % 10^k`, because `D ∣ 10^k`); the
second by the Unified Osculator Theorem (`DivisibilityTruncationGeneralOQ01`)
applied to `m`.

That such a decomposition `d = D · m` exists for every `d > 0` is the fundamental
theorem of arithmetic (take `D = 2^{v₂(d)} · 5^{v₅(d)}` and `m = d / D`). Here we
formalize the *test itself* as a theorem parametrized by the decomposition, the
two structural lemmas it rests on, and worked instances (d = 6, 12, 14).
-/

import Proofs.DivisibilityTruncationGeneralOQ01
import Mathlib.Tactic

open Nat

namespace CombinedOsculator

-- ============================================================================
-- Part I: Last-k-digits test for the 2,5-part
-- ============================================================================

/-- **Last-k-digits test.** If `D ∣ 10^k`, then divisibility by `D` is decided by
    the last `k` decimal digits of `n`, i.e. by `n % 10^k`.

    This is the standard rule "a number is divisible by `2^a` (resp. `5^b`) iff its
    last `max a b` digits are", stated for any `D` dividing a power of ten. -/
theorem dvd_iff_dvd_mod_pow (D n k : ℕ) (hD : D ∣ 10 ^ k) :
    D ∣ n ↔ D ∣ n % 10 ^ k := by
  have hmterm : D ∣ 10 ^ k * (n / 10 ^ k) := hD.mul_right _
  have hsplit : 10 ^ k * (n / 10 ^ k) + n % 10 ^ k = n := Nat.div_add_mod n (10 ^ k)
  constructor
  · intro h
    have hsub : D ∣ n - 10 ^ k * (n / 10 ^ k) := Nat.dvd_sub' h hmterm
    have heq : n - 10 ^ k * (n / 10 ^ k) = n % 10 ^ k := by omega
    rwa [heq] at hsub
  · intro h
    have hsum := dvd_add hmterm h
    rwa [hsplit] at hsum

-- ============================================================================
-- Part II: CRT split for coprime factors
-- ============================================================================

/-- **Chinese Remainder Theorem (divisibility form).** If `gcd(D, m) = 1`, then
    `D · m ∣ n ↔ D ∣ n ∧ m ∣ n`. -/
theorem dvd_mul_iff_of_coprime {D m : ℕ} (hcop : Nat.Coprime D m) (n : ℕ) :
    D * m ∣ n ↔ D ∣ n ∧ m ∣ n := by
  constructor
  · intro h
    exact ⟨(dvd_mul_right D m).trans h, (dvd_mul_left m D).trans h⟩
  · rintro ⟨h1, h2⟩
    exact hcop.mul_dvd_of_dvd_of_dvd h1 h2

-- ============================================================================
-- Part III: The Combined Osculator Theorem
-- ============================================================================

/-- **Combined Osculator Theorem.**

    Let `d = D · m` with
      * `D ∣ 10^k`           (D built from the 2- and 5-parts of d),
      * `gcd(D, m) = 1`,
      * `gcd(m, 10) = 1`     (m the osculator-testable part), and
      * osculator `c` for `m`, i.e. `m ∣ 10c - 1`.

    Then divisibility by `d` is decided by combining the last-`k`-digits test on
    `D` with the osculator test on `m`:

      `d ∣ n  ↔  (D ∣ n % 10^k)  ∧  ((m : ℤ) ∣ n/10 + c·(n%10))`.

    This answers the open question: the osculator framework extends to **all**
    divisors, not only those coprime to 10. -/
theorem combined_osculator (D m k : ℕ) (c : ℤ) (n : ℕ)
    (hD : D ∣ 10 ^ k)
    (hcopDm : Nat.Coprime D m)
    (hcop10 : IsCoprime (m : ℤ) 10)
    (hc : (m : ℤ) ∣ 10 * c - 1) :
    D * m ∣ n ↔
      (D ∣ n % 10 ^ k) ∧ ((m : ℤ) ∣ (↑(n / 10) + c * ↑(n % 10))) := by
  have hm : m ∣ n ↔ (m : ℤ) ∣ (↑(n / 10) + c * ↑(n % 10)) := by
    rw [← Int.natCast_dvd_natCast]
    exact UnifiedOsculator.unified_osculator m c n hcop10 hc
  rw [dvd_mul_iff_of_coprime hcopDm n, dvd_iff_dvd_mod_pow D n k hD, hm]

-- ============================================================================
-- Part IV: Worked instances
-- ============================================================================

/-- d = 6 = 2 · 3. The 2-part needs the last digit (k = 1); the 3-part uses
    osculator c = 1 (since 3 ∣ 10·1 - 1 = 9). -/
theorem six_combined (n : ℕ) :
    6 ∣ n ↔ (2 ∣ n % 10) ∧ ((3 : ℤ) ∣ (↑(n / 10) + ↑(n % 10))) := by
  have h := combined_osculator 2 3 1 1 n (by norm_num) (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide)) ⟨3, by norm_num⟩
  simpa using h

/-- d = 12 = 4 · 3. The 4-part needs the last *two* digits (k = 2); the 3-part
    uses osculator c = 1. -/
theorem twelve_combined (n : ℕ) :
    12 ∣ n ↔ (4 ∣ n % 100) ∧ ((3 : ℤ) ∣ (↑(n / 10) + ↑(n % 10))) := by
  have h := combined_osculator 4 3 2 1 n (by norm_num) (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide)) ⟨3, by norm_num⟩
  simpa using h

/-- d = 14 = 2 · 7. The 2-part uses the last digit (k = 1); the 7-part uses
    osculator c = 5 (since 7 ∣ 10·5 - 1 = 49). -/
theorem fourteen_combined (n : ℕ) :
    14 ∣ n ↔ (2 ∣ n % 10) ∧ ((7 : ℤ) ∣ (↑(n / 10) + 5 * ↑(n % 10))) := by
  have h := combined_osculator 2 7 1 5 n (by norm_num) (by decide)
    (Int.isCoprime_iff_gcd_eq_one.mpr (by decide)) ⟨7, by norm_num⟩
  simpa using h

-- ============================================================================
-- Part V: Sanity checks
-- ============================================================================

example : 6 ∣ 312 := by native_decide
example : 12 ∣ 144 := by native_decide
example : 14 ∣ 98 := by native_decide
example : ¬ (6 ∣ 100) := by native_decide

#check @combined_osculator
#check @dvd_iff_dvd_mod_pow
#check @dvd_mul_iff_of_coprime

end CombinedOsculator
