/-
  Aristotle targets for DivisibilityByThreeOQ01OQ02 (Digital Root Convergence)
  Routine list combinatorics for automated proof search.
  See DivisibilityByThreeOQ01OQ02.lean for the main formalization.

  One sorry remains in digitSum_pos: for n ≥ 10, proving that the digit sum
  is positive. The proof uses two Mathlib lemmas:
    - Nat.getLast_digit_ne_zero: the leading (last) digit of base-10 n is nonzero
    - List.single_le_sum: any element of a list of nonneg naturals ≤ the sum

  The last digit is nonzero and ≤ the sum, so the sum ≥ 1 > 0.
-/
import Mathlib
import Proofs.DivisibilityByThreeOQ01

open Nat

namespace DivisibilityByThreeOQ01OQ02Aristotle

/-- Base-10 digit sum (matches definition in main file) -/
def digitSum (n : ℕ) : ℕ := (Nat.digits 10 n).sum

/-
HELPER: Digits list of n is nonempty when n > 0.
-/
lemma digits_nonempty {n : ℕ} (hn : 0 < n) : Nat.digits 10 n ≠ [] := by
  rw [Nat.digits_ne_nil_iff_ne_zero]
  omega

/-
HELPER: The last digit of n in base 10 is at least 1 when n > 0.
By Nat.getLast_digit_ne_zero: for base b > 1 and n ≠ 0,
the last element of Nat.digits b n is nonzero.
-/
lemma last_digit_pos {n : ℕ} (hn : 0 < n) :
    0 < (Nat.digits 10 n).getLast (digits_nonempty hn) := by
  have hne : n ≠ 0 := by omega
  have h := Nat.getLast_digit_ne_zero 10 (by norm_num) hne
  -- h : (Nat.digits 10 n).getLast _ ≠ 0  (proof irrelevance ensures same getLast value)
  omega

/-
TARGET
digitSum n > 0 when n > 0.

Full proof for n < 10: interval_cases + native_decide (already done in main file).
Sorry: the case n ≥ 10.

Strategy for n ≥ 10:
  1. Digits list is nonempty: Nat.digits 10 n ≠ []  (digits_nonempty)
  2. Last digit is positive: getLast (Nat.digits 10 n) ≠ 0  (last_digit_pos)
  3. Last digit ∈ Nat.digits 10 n  (List.getLast_mem)
  4. Last digit ≤ sum  (List.single_le_sum with nonneg elements)
  5. So sum ≥ last digit ≥ 1
-/
theorem digitSum_pos (n : ℕ) (hn : 0 < n) : 0 < digitSum n := by
  unfold digitSum
  rcases lt_or_ge n 10 with h | h
  · interval_cases n <;> native_decide
  · -- n ≥ 10: use last_digit_pos + List.single_le_sum
    -- Digits list is nonempty; last digit is positive (by last_digit_pos);
    -- last digit ∈ list (List.getLast_mem); last digit ≤ sum (List.single_le_sum)
    sorry

end DivisibilityByThreeOQ01OQ02Aristotle
