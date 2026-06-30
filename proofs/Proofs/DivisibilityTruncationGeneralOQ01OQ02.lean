/-
# Osculator Divisibility Rules: Extending Coverage Beyond 19

Open Question (from divisibility-truncation-general / OQ01):
  The Unified Osculator Theorem (`unified_osculator`) and its negative
  variant (`neg_osculator_from_unified`) give osculator divisibility
  rules for any divisor coprime to 10. The OQ01 file instantiated these
  for d = 7, 11, 13, 17, 19. Can the coverage be extended to the next
  primes coprime to 10: 23, 29, 31, 37, 41, 43?

Answer: YES — purely by instantiation. For each prime d there is a
unique smallest osculator. We pick whichever of the positive osculator
(d | 10c - 1) or negative osculator (d | 10c + 1) has the smaller
constant:

  | d  | osculator | c  | identity         |
  |----|-----------|----|------------------|
  | 23 | positive  | 7  | 10·7  - 1 = 69  = 23·3 |
  | 29 | positive  | 3  | 10·3  - 1 = 29  = 29·1 |
  | 31 | negative  | 3  | 10·3  + 1 = 31  = 31·1 |
  | 37 | negative  | 11 | 10·11 + 1 = 111 = 37·3 |
  | 41 | negative  | 4  | 10·4  + 1 = 41  = 41·1 |
  | 43 | positive  | 13 | 10·13 - 1 = 129 = 43·3 |

Each rule reduces divisibility testing of n to a smaller number
n/10 ± c·(n%10), exactly as for the classical small-prime rules.
No new mathematics is required: every theorem below is a one-line
application of the general osculator theorems proved in OQ01.
-/

import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Tactic
import Proofs.DivisibilityTruncationGeneralOQ01

open Nat

namespace OsculatorExtended

open UnifiedOsculator

/-- d=23 via positive osculator c=7 (10·7 - 1 = 69 = 23·3). -/
theorem twentythree_unified (n : ℕ) :
    (23 : ℤ) ∣ n ↔ (23 : ℤ) ∣ (↑(n / 10) + 7 * ↑(n % 10)) :=
  unified_osculator 23 7 n (by decide) ⟨3, by norm_num⟩

/-- d=29 via positive osculator c=3 (10·3 - 1 = 29 = 29·1). -/
theorem twentynine_unified (n : ℕ) :
    (29 : ℤ) ∣ n ↔ (29 : ℤ) ∣ (↑(n / 10) + 3 * ↑(n % 10)) :=
  unified_osculator 29 3 n (by decide) ⟨1, by norm_num⟩

/-- d=31 via negative osculator c=3 (10·3 + 1 = 31 = 31·1). -/
theorem thirtyone_unified (n : ℕ) :
    (31 : ℤ) ∣ n ↔ (31 : ℤ) ∣ (↑(n / 10) - 3 * ↑(n % 10)) :=
  neg_osculator_from_unified 31 3 n (by decide) ⟨1, by norm_num⟩

/-- d=37 via negative osculator c=11 (10·11 + 1 = 111 = 37·3). -/
theorem thirtyseven_unified (n : ℕ) :
    (37 : ℤ) ∣ n ↔ (37 : ℤ) ∣ (↑(n / 10) - 11 * ↑(n % 10)) :=
  neg_osculator_from_unified 37 11 n (by decide) ⟨3, by norm_num⟩

/-- d=41 via negative osculator c=4 (10·4 + 1 = 41 = 41·1). -/
theorem fortyone_unified (n : ℕ) :
    (41 : ℤ) ∣ n ↔ (41 : ℤ) ∣ (↑(n / 10) - 4 * ↑(n % 10)) :=
  neg_osculator_from_unified 41 4 n (by decide) ⟨1, by norm_num⟩

/-- d=43 via positive osculator c=13 (10·13 - 1 = 129 = 43·3). -/
theorem fortythree_unified (n : ℕ) :
    (43 : ℤ) ∣ n ↔ (43 : ℤ) ∣ (↑(n / 10) + 13 * ↑(n % 10)) :=
  unified_osculator 43 13 n (by decide) ⟨3, by norm_num⟩

-- ============================================================================
-- Sanity checks: the osculator identities hold numerically
-- ============================================================================

example : (23 : ℤ) ∣ (10 * 7 - 1) := ⟨3, by norm_num⟩
example : (29 : ℤ) ∣ (10 * 3 - 1) := ⟨1, by norm_num⟩
example : (31 : ℤ) ∣ (10 * 3 + 1) := ⟨1, by norm_num⟩
example : (37 : ℤ) ∣ (10 * 11 + 1) := ⟨3, by norm_num⟩
example : (41 : ℤ) ∣ (10 * 4 + 1) := ⟨1, by norm_num⟩
example : (43 : ℤ) ∣ (10 * 13 - 1) := ⟨3, by norm_num⟩

-- Worked example: 23 ∣ 161 (= 23·7). Rule: 161 → 16 + 7·1 = 23, and 23 ∣ 23.
example : 23 ∣ 161 := by native_decide

#check twentythree_unified
#check fortythree_unified

end OsculatorExtended
