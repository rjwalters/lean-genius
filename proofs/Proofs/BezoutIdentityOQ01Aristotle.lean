/-
  Aristotle targets for Bezout Identity OQ01: Extended Euclidean Algorithm
  Routine supporting lemmas for automated proof search.
  See BezoutIdentityOQ01.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main results (extGcd correctness and GCD correctness - fully proved)
  - Routine properties of Nat.gcd used as supporting facts
  - No definition sorries
  - No axioms

  Included targets (5):
  - gcd_self: gcd a a = a
  - gcd_comm: gcd a b = gcd b a
  - gcd_zero_left: gcd 0 a = a
  - gcd_dvd_left: gcd a b ∣ a
  - gcd_pos_of_pos_left: 0 < a → 0 < gcd a b
-/
import Mathlib.Data.Nat.GCD.Basic

namespace BezoutIdentityOQ01Aristotle

-- Routine: gcd a a = a.
-- Standard identity: gcd of a number with itself is itself.
theorem gcd_self (a : ℕ) : Nat.gcd a a = a := by
  sorry

-- Routine: gcd is symmetric.
-- gcd a b = gcd b a.
theorem gcd_comm (a b : ℕ) : Nat.gcd a b = Nat.gcd b a := by
  sorry

-- Routine: gcd 0 a = a.
-- Zero is the identity for gcd.
theorem gcd_zero_left (a : ℕ) : Nat.gcd 0 a = a := by
  sorry

-- Routine: gcd a b divides a.
-- The gcd divides both arguments.
theorem gcd_dvd_left (a b : ℕ) : Nat.gcd a b ∣ a := by
  sorry

-- Routine: if a > 0 then gcd a b > 0.
-- The gcd is positive whenever either argument is positive.
theorem gcd_pos_of_pos_left (a b : ℕ) (ha : 0 < a) : 0 < Nat.gcd a b := by
  sorry

end BezoutIdentityOQ01Aristotle
