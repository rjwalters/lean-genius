/-
  Aristotle targets for Erdős Problem #674
  Routine supporting lemmas for automated proof search.
  See Erdos674Problem.lean for the main formalization.

  Criteria for inclusion:
  - NOT the main open conjecture or deep theorems (Ko, Schinzel, Dem'janenko, etc.)
  - Known results likely provable from Mathlib (arithmetic, algebraic identities)
  - Clean theorem statements with no definition sorries
  - No axioms
-/
import Mathlib

namespace Erdos674Aristotle

open Nat

-- ═══════════════════════════════════════════════════════════════════
-- Section 1: Ko's Example — Arithmetic Verification
-- ═══════════════════════════════════════════════════════════════════

/-- Ko's example: x = 2^12 · 3^6. -/
def koX : ℕ := 2 ^ 12 * 3 ^ 6

/-- Ko's example: y = 2^8 · 3^8. -/
def koY : ℕ := 2 ^ 8 * 3 ^ 8

/-- Ko's example: z = 2^11 · 3^7. -/
def koZ : ℕ := 2 ^ 11 * 3 ^ 7

/-- koX > 1. -/
theorem koX_gt_one : koX > 1 := by
  unfold koX; norm_num

/-- koY > 1. -/
theorem koY_gt_one : koY > 1 := by
  unfold koY; norm_num

/-- koZ > 1. -/
theorem koZ_gt_one : koZ > 1 := by
  unfold koZ; norm_num

/-- Ko's family satisfies 4xy = z². -/
theorem ko_family_ratio : 4 * koX * koY = koZ ^ 2 := by unfold koX koY koZ; norm_num

/-- koX = 2985984. -/
theorem koX_value : koX = 2985984 := by unfold koX; norm_num

/-- koY = 1679616. -/
theorem koY_value : koY = 1679616 := by unfold koY; norm_num

/-- koZ = 4478976. -/
theorem koZ_value : koZ = 4478976 := by unfold koZ; norm_num

-- ═══════════════════════════════════════════════════════════════════
-- Section 2: Symmetry and Small Cases
-- ═══════════════════════════════════════════════════════════════════

/-- Swapping x and y preserves the product x^x * y^y. -/
theorem swap_preserves_eq (x y z : ℕ) :
    x ^ x * y ^ y = z ^ z → y ^ y * x ^ x = z ^ z := by
  intro h; rw [mul_comm]; exact h

-- ═══════════════════════════════════════════════════════════════════
-- Section 3: GCD and Divisibility Lemmas
-- ═══════════════════════════════════════════════════════════════════

/-- If gcd(x, y) = 1 and p | x, then ¬(p | y). -/
theorem coprime_prime_div (x y p : ℕ) (hcop : x.gcd y = 1)
    (hp : p.Prime) (hdvd : p ∣ x) : ¬(p ∣ y) := by
  intro hdy
  have := Nat.Prime.dvd_gcd hp hdvd hdy
  rw [hcop] at this
  exact Nat.Prime.one_lt hp |>.not_le (Nat.le_of_dvd (by omega) this)

/-- gcd(x, y) > 1 ↔ gcd(x, y) ≠ 1 for x, y > 1. -/
theorem gcd_gt_one_iff (x y : ℕ) (hx : x > 1) (hy : y > 1) :
    x.gcd y > 1 ↔ x.gcd y ≠ 1 := by
  constructor
  · intro h; omega
  · intro h
    have hpos : x.gcd y > 0 := Nat.pos_of_ne_zero (by intro h0; simp [h0] at h)
    omega

-- ═══════════════════════════════════════════════════════════════════
-- Section 4: Power and Exponentiation Identities
-- ═══════════════════════════════════════════════════════════════════

/-- x^(2x) = (x^x)^2. -/
theorem pow_double_eq_sq (x : ℕ) : x ^ (2 * x) = (x ^ x) ^ 2 := by
  rw [sq, ← pow_add, two_mul]

/-- x^(2x) = x^x * x^x. -/
theorem pow_double_eq_mul (x : ℕ) : x ^ (2 * x) = x ^ x * x ^ x := by
  rw [pow_double_eq_sq, sq]

/-- For a, b > 1 with a^a * b^b = c^c, we have c > 1. -/
theorem solution_z_gt_one (a b c : ℕ) (ha : a > 1) (hb : b > 1)
    (heq : a ^ a * b ^ b = c ^ c) : c > 1 := by
  by_contra hc
  push_neg at hc
  interval_cases c
  · simp at heq; have := mul_pos (Nat.pos_of_ne_zero (by positivity)) (Nat.pos_of_ne_zero (by positivity)); omega
  · simp at heq; have h1 := Nat.one_lt_pow ha; have h2 := Nat.one_lt_pow hb; nlinarith

end Erdos674Aristotle
