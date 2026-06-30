import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

/-
# The Unified 7-11-13 Divisibility Rule  (divisibility-rules-oq-04-oq-01)

## Open Question (parent: divisibility-rules-oq-04)
"Prove the unified 7-11-13 rule directly: `n` is divisible by each of 7, 11, 13
iff that prime divides the alternating sum of three-digit blocks, exhibiting the
single base-1000 grouping (`1001 = 7·11·13`) behind all three tests."

The parent entry `divisibility-rules-oq-04` already records the three-digit
block-alternating test *for 11* as one of three rules keyed to `10`, `100`,
`1000` mod 11.  This entry isolates the genuinely unifying phenomenon: the
**single** base-1000 grouping `b₀ - b₁ + b₂ - ⋯` simultaneously detects
divisibility by 7, 11 **and** 13, because all three primes divide `1001`, and
`1000 ≡ -1 (mod m)` precisely when `m ∣ 1001`.

Rather than re-prove the 11-case, we factor the argument through one parametric
lemma `dvd_iff_dvd_blockAltSum`: for *any* modulus `m ∣ 1001`, the same block
alternating sum is the divisibility certificate.  The classical 7/11/13 rules,
their conjunction, and the combined `1001`-rule are then one-line corollaries,
making the shared `1001` structure explicit.  All results are fully verified
(0 axioms): every step is a specialization of Mathlib's base-`b` digit machinery
(`Nat.dvd_iff_dvd_ofDigits`, `Nat.ofDigits_neg_one`, `Nat.zmodeq_ofDigits_digits`)
plus elementary coprimality.
-/

namespace DivisibilityRulesOQ04OQ01

open Nat

/-- The signed alternating sum of the base-1000 blocks (the three-decimal-digit
groups, read from least significant): `b₀ - b₁ + b₂ - ⋯`.  This single quantity is
the divisibility certificate shared by 7, 11 and 13. -/
def blockAltSum (n : ℕ) : ℤ :=
  ((Nat.digits 1000 n).map fun d : ℕ => (d : ℤ)).alternatingSum

/-- The arithmetic fact behind everything: `1001 = 7 · 11 · 13`. -/
theorem one_thousand_one_eq : (1001 : ℕ) = 7 * 11 * 13 := by norm_num

/-- **Unified block-alternating divisibility test.** For *any* modulus `m` dividing
`1001`, `m ∣ n` iff `m` divides the alternating sum of the base-1000 blocks of `n`.

This is the single theorem behind all three classical rules: `1000 ≡ -1 (mod m)`
holds exactly when `m ∣ (1000 - (-1)) = 1001`, so the one base-1000 grouping serves
every divisor of `1001 = 7·11·13` at once. -/
theorem dvd_iff_dvd_blockAltSum (m n : ℕ) (hm : (m : ℤ) ∣ 1001) :
    m ∣ n ↔ (m : ℤ) ∣ blockAltSum n := by
  have h : (m : ℤ) ∣ (1000 : ℤ) - (-1) := by simpa using hm
  have t := Nat.dvd_iff_dvd_ofDigits m 1000 (-1 : ℤ) h n
  rw [Nat.ofDigits_neg_one] at t
  exact t

/-- **Divisibility-by-7 rule** via the base-1000 alternating block sum. -/
theorem seven_dvd_iff (n : ℕ) : 7 ∣ n ↔ (7 : ℤ) ∣ blockAltSum n :=
  dvd_iff_dvd_blockAltSum 7 n (by norm_num)

/-- **Divisibility-by-11 rule** via the *same* base-1000 alternating block sum. -/
theorem eleven_dvd_iff (n : ℕ) : 11 ∣ n ↔ (11 : ℤ) ∣ blockAltSum n :=
  dvd_iff_dvd_blockAltSum 11 n (by norm_num)

/-- **Divisibility-by-13 rule** via the *same* base-1000 alternating block sum. -/
theorem thirteen_dvd_iff (n : ℕ) : 13 ∣ n ↔ (13 : ℤ) ∣ blockAltSum n :=
  dvd_iff_dvd_blockAltSum 13 n (by norm_num)

/-- **The unified statement, as asked.** `n` is divisible by each of 7, 11, 13 iff
that prime divides the alternating sum of the three-digit blocks — all three tests
read off the one quantity `blockAltSum n`. -/
theorem unified_7_11_13 (n : ℕ) :
    (7 ∣ n ↔ (7 : ℤ) ∣ blockAltSum n) ∧
    (11 ∣ n ↔ (11 : ℤ) ∣ blockAltSum n) ∧
    (13 ∣ n ↔ (13 : ℤ) ∣ blockAltSum n) :=
  ⟨seven_dvd_iff n, eleven_dvd_iff n, thirteen_dvd_iff n⟩

/-- Divisibility by all of 7, 11, 13 is exactly divisibility by their product
`1001` (they are pairwise coprime). -/
theorem all_three_dvd_iff_dvd_1001 (n : ℕ) :
    (7 ∣ n ∧ 11 ∣ n ∧ 13 ∣ n) ↔ 1001 ∣ n := by
  constructor
  · rintro ⟨h7, h11, h13⟩
    have h77 : 77 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h7 h11
    have h1001 : 77 * 13 ∣ n := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h77 h13
    simpa using h1001
  · intro h
    exact ⟨dvd_trans (by norm_num) h, dvd_trans (by norm_num) h, dvd_trans (by norm_num) h⟩

/-- **Combined `1001`-rule.** The very same base-1000 alternating block sum tests
divisibility by `1001 = 7·11·13` itself: `n` is a multiple of all three primes iff
`1001` divides `blockAltSum n`. -/
theorem all_three_dvd_iff_blockAltSum (n : ℕ) :
    (7 ∣ n ∧ 11 ∣ n ∧ 13 ∣ n) ↔ (1001 : ℤ) ∣ blockAltSum n := by
  rw [all_three_dvd_iff_dvd_1001]
  exact dvd_iff_dvd_blockAltSum 1001 n (by norm_num)

/-- **Underlying congruence.** `n` is congruent to its base-1000 alternating block
sum modulo `1001` — the residue identity (`1000 ≡ -1 (mod 1001)`) that powers every
one of the rules above. -/
theorem modEq_blockAltSum (n : ℕ) : (n : ℤ) ≡ blockAltSum n [ZMOD 1001] := by
  have h : (1000 : ℤ) ≡ (-1 : ℤ) [ZMOD 1001] := Int.modEq_iff_dvd.mpr (by norm_num)
  have t := Nat.zmodeq_ofDigits_digits 1001 1000 (-1 : ℤ) h n
  rwa [Nat.ofDigits_neg_one] at t

end DivisibilityRulesOQ04OQ01
