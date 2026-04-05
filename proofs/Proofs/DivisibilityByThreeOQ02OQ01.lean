/-
  Repunit Divisibility — Order-of-10 Characterization
  Open Question OQ-01 from DivisibilityByThreeOQ02

  Question: For which k does d ∣ R(k)?
  The complete characterization: d ∣ R(k) ↔ orderOf (10 : ZMod d) ∣ k,
  provided gcd(d, 9) = 1 and 1 < d.

  Key insight: In ZMod d we have 9·R(k) + 1 = 10^k (exact ring identity).
  Since gcd(d,9)=1, the element 9 is a unit in ZMod d, so:
    d ∣ R(k) ↔ R(k) ≡ 0 (mod d)
             ↔ 9·R(k) ≡ 0 (mod d)
             ↔ 10^k ≡ 1 (mod d)
             ↔ orderOf(10 mod d) ∣ k

  Note: hypothesis is Coprime d 9, not Coprime d 10.
  d=3 satisfies gcd(3,10)=1 but 3∤R(1)=1; the correct condition is gcd(d,9)=1.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

-- Local definition of repunit (self-contained to avoid parent module errors)
private def repunit : ℕ → ℕ
  | 0 => 0
  | n + 1 => repunit n * 10 + 1

/-- The core ZMod identity: 9·R(k) + 1 = 10^k in any ZMod d. -/
private theorem repunit_ZMod_aux (d k : ℕ) :
    (9 : ZMod d) * (repunit k : ZMod d) + 1 = (10 : ZMod d) ^ k := by
  induction k with
  | zero => simp [repunit]
  | succ n ih =>
    have hcast : (repunit (n + 1) : ZMod d) = repunit n * 10 + 1 := by
      simp [repunit, Nat.cast_add, Nat.cast_mul]
    rw [hcast, pow_succ]
    linear_combination 10 * ih

/-- d divides the k-th repunit iff the multiplicative order of 10 mod d divides k.
    Requires gcd(d, 9) = 1 and 1 < d. -/
theorem repunit_dvd_iff_orderOf (d k : ℕ) (hd : 1 < d) (hd9 : Nat.Coprime d 9) :
    d ∣ repunit k ↔ orderOf (10 : ZMod d) ∣ k := by
  rw [← ZMod.natCast_eq_zero_iff, orderOf_dvd_iff_pow_eq_one]
  -- Goal: (repunit k : ZMod d) = 0 ↔ (10 : ZMod d)^k = 1
  constructor
  · intro hR
    -- R(k) ≡ 0 mod d ⟹ 9·R(k) = 0 ⟹ 10^k = 1 (via 9·R(k)+1 = 10^k)
    have h10 := repunit_ZMod_aux d k
    rw [hR, mul_zero, zero_add] at h10
    exact h10.symm
  · intro h10k
    -- 10^k = 1 ⟹ 9·R(k) = 0 in ZMod d ⟹ d ∣ 9·R(k) ⟹ d ∣ R(k) (by Coprime d 9)
    have h9R_ZMod : (9 : ZMod d) * (repunit k : ZMod d) = 0 := by
      linear_combination (repunit_ZMod_aux d k).trans h10k
    have h9R_dvd : d ∣ 9 * repunit k :=
      (ZMod.natCast_eq_zero_iff _ _).mp (by push_cast; exact h9R_ZMod)
    exact (ZMod.natCast_eq_zero_iff _ _).mpr (hd9.dvd_of_dvd_mul_left h9R_dvd)

-- Concrete verifications
example : 7 ∣ repunit 6 := by native_decide
example : ¬(7 ∣ repunit 5) := by native_decide
example : 11 ∣ repunit 2 := by native_decide
example : ¬(11 ∣ repunit 1) := by native_decide
example : 37 ∣ repunit 3 := by native_decide
example : ¬(37 ∣ repunit 2) := by native_decide
