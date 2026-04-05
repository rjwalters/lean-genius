/-
  Minimal Period for Digit-Block Divisibility Rules
  OQ-01-01 from DivisibilityRulesOQ01OQ01

  The digit-block divisibility rule "d ∣ n ↔ d ∣ sum_of_k_digit_blocks(n)"
  holds for period k iff 10^k ≡ 1 (mod d) iff orderOf (10 : ZMod d) ∣ k.

  In particular, the minimal positive period is exactly orderOf (10 : ZMod d).
  Generalizes to any base b with gcd(d,b)=1: minimal period = orderOf (b : ZMod d).

  Key connections:
  - 10^k % d = 1 ↔ orderOf (10 : ZMod d) ∣ k    [orderOf_dvd_iff_pow_eq_one]
  - 10^k % d = 1 → d ∣ n ↔ d ∣ digits_sum(n, 10^k) [Nat.modEq_digits_sum]
  - orderOf (10 : ZMod d) is minimal: any k with 10^k ≡ 1 satisfies orderOf ≤ k

  Parent: DivisibilityRulesOQ01OQ01.lean (existence via Euler's theorem)
  Related: DivisibilityByThreeOQ02OQ01.lean (repunit biconditional via orderOf)
-/
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

open BigOperators

namespace DivisibilityRulesOQ01OQ01OQ01

-- ═══════════════════════════════════════════════════════════════════
-- PART I: 10^k ≡ 1 (mod d) ↔ orderOf (10 : ZMod d) ∣ k
-- ═══════════════════════════════════════════════════════════════════

/-- 10^k ≡ 1 (mod d) iff (10 : ZMod d)^k = 1 (for d > 1). -/
private theorem pow_mod_one_iff_ZMod_pow_eq_one (b d k : ℕ) (hd : 1 < d) :
    b ^ k % d = 1 ↔ (b : ZMod d) ^ k = 1 := by
  haveI : NeZero d := ⟨by omega⟩
  constructor
  · intro h
    have hmod : b ^ k ≡ 1 [MOD d] := by unfold Nat.ModEq; rw [h, Nat.mod_eq_of_lt hd]
    have hcast := (ZMod.natCast_eq_natCast_iff (b ^ k) 1 d).mpr hmod
    push_cast at hcast
    exact hcast
  · intro h
    have hcast : ((b ^ k : ℕ) : ZMod d) = ((1 : ℕ) : ZMod d) := by push_cast; exact h
    rw [ZMod.natCast_eq_natCast_iff] at hcast
    unfold Nat.ModEq at hcast
    rwa [Nat.mod_eq_of_lt hd] at hcast

/-- The digit-block rule holds at period k iff orderOf (10 : ZMod d) divides k. -/
theorem period_iff_orderOf_dvd (hd : 1 < d) (k : ℕ) :
    10 ^ k % d = 1 ↔ orderOf (10 : ZMod d) ∣ k :=
  (pow_mod_one_iff_ZMod_pow_eq_one 10 d k hd).trans orderOf_dvd_iff_pow_eq_one.symm

-- ═══════════════════════════════════════════════════════════════════
-- PART II: EULER'S THEOREM GIVES FINITE ORDER
-- ═══════════════════════════════════════════════════════════════════

/-- When gcd(d,b)=1 and d>1, (b : ZMod d)^φ(d) = 1 (Euler's theorem). -/
private theorem pow_totient_eq_one (b d : ℕ) (hd : 1 < d) (hcop : Nat.Coprime d b) :
    (b : ZMod d) ^ d.totient = 1 := by
  haveI : NeZero d := ⟨by omega⟩
  let u := ZMod.unitOfCoprime b hcop.symm
  have hpow_unit : u ^ d.totient = 1 := ZMod.pow_totient u
  have hcoe : (u : ZMod d) = b := by simp [u, ZMod.unitOfCoprime]
  have h : (u : ZMod d) ^ d.totient = 1 := by
    have := congr_arg Units.val hpow_unit
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at this
    exact_mod_cast this
  rwa [hcoe] at h

/-- orderOf (b : ZMod d) is positive when gcd(d,b)=1 and d>1. -/
theorem orderOf_pos_of_coprime (b d : ℕ) (hd : 1 < d) (hcop : Nat.Coprime d b) :
    0 < orderOf (b : ZMod d) := by
  exact Nat.pos_of_dvd_of_pos
    (orderOf_dvd_of_pow_eq_one (pow_totient_eq_one b d hd hcop))
    (Nat.totient_pos.mpr (by omega))

-- ═══════════════════════════════════════════════════════════════════
-- PART III: DIGIT-BLOCK RULE FROM PERIOD
-- ═══════════════════════════════════════════════════════════════════

/-- If orderOf (10 : ZMod d) ∣ k, the digit-block rule holds for all n. -/
theorem digit_block_rule_of_orderOf_dvd (hd : 1 < d) (hcop : Nat.Coprime d 10)
    (k : ℕ) (hk : orderOf (10 : ZMod d) ∣ k) (n : ℕ) :
    d ∣ n ↔ d ∣ (Nat.digits (10 ^ k) n).sum := by
  have hmod : 10 ^ k % d = 1 := (period_iff_orderOf_dvd hd k).mpr hk
  exact Nat.ModEq.dvd_iff (Nat.modEq_digits_sum d (10 ^ k) hmod n) (dvd_refl d)

/-- The rule holds at the minimal period k₀ = orderOf (10 : ZMod d). -/
theorem digit_block_rule_at_orderOf (hd : 1 < d) (hcop : Nat.Coprime d 10) (n : ℕ) :
    d ∣ n ↔ d ∣ (Nat.digits (10 ^ orderOf (10 : ZMod d)) n).sum :=
  digit_block_rule_of_orderOf_dvd hd hcop _ (dvd_refl _) n

-- ═══════════════════════════════════════════════════════════════════
-- PART IV: MINIMALITY OF orderOf (10 : ZMod d)
-- ═══════════════════════════════════════════════════════════════════

/-- orderOf (10 : ZMod d) ≤ any positive k with 10^k ≡ 1 (mod d). -/
theorem orderOf_le_of_period (hd : 1 < d) (k : ℕ) (hk_pos : 0 < k)
    (hk : 10 ^ k % d = 1) : orderOf (10 : ZMod d) ≤ k :=
  Nat.le_of_dvd hk_pos
    (orderOf_dvd_of_pow_eq_one ((pow_mod_one_iff_ZMod_pow_eq_one 10 d k hd).mp hk))

/-- The three defining properties of the minimal period. -/
theorem orderOf_is_minimal_period (hd : 1 < d) (hcop : Nat.Coprime d 10) :
    let k₀ := orderOf (10 : ZMod d)
    0 < k₀ ∧                                    -- positive
    10 ^ k₀ % d = 1 ∧                           -- rule holds at k₀
    ∀ k > 0, 10 ^ k % d = 1 → k₀ ≤ k := by     -- minimal
  refine ⟨orderOf_pos_of_coprime 10 d hd hcop,
          (period_iff_orderOf_dvd hd _).mpr (dvd_refl _),
          fun k hk_pos hk => orderOf_le_of_period hd k hk_pos hk⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART V: GENERALIZATION TO BASE b
-- ═══════════════════════════════════════════════════════════════════

/-- For base b with gcd(d,b)=1, the period k iff orderOf (b : ZMod d) ∣ k. -/
theorem period_iff_orderOf_dvd_base_b (b d : ℕ) (hd : 1 < d) (k : ℕ) :
    b ^ k % d = 1 ↔ orderOf (b : ZMod d) ∣ k :=
  (pow_mod_one_iff_ZMod_pow_eq_one b d k hd).trans orderOf_dvd_iff_pow_eq_one.symm

/-- Base-b digit rule holds for period k when orderOf (b : ZMod d) ∣ k. -/
theorem digit_block_rule_base_b (b d : ℕ) (hd : 1 < d) (hcop : Nat.Coprime d b)
    (k : ℕ) (hk : orderOf (b : ZMod d) ∣ k) (n : ℕ) :
    d ∣ n ↔ d ∣ (Nat.digits (b ^ k) n).sum := by
  have hmod : b ^ k % d = 1 := (period_iff_orderOf_dvd_base_b b d hd k).mpr hk
  exact Nat.ModEq.dvd_iff (Nat.modEq_digits_sum d (b ^ k) hmod n) (dvd_refl d)

/-- The minimal period for base b is orderOf (b : ZMod d). -/
theorem orderOf_base_b_is_minimal_period (b d : ℕ) (hd : 1 < d) (hcop : Nat.Coprime d b) :
    let k₀ := orderOf (b : ZMod d)
    0 < k₀ ∧                                    -- positive
    b ^ k₀ % d = 1 ∧                            -- rule holds at k₀
    ∀ k > 0, b ^ k % d = 1 → k₀ ≤ k := by      -- minimal
  refine ⟨orderOf_pos_of_coprime b d hd hcop,
          (period_iff_orderOf_dvd_base_b b d hd _).mpr (dvd_refl _),
          fun k hk_pos hk => Nat.le_of_dvd hk_pos
            (orderOf_dvd_of_pow_eq_one
              ((pow_mod_one_iff_ZMod_pow_eq_one b d k hd).mp hk))⟩

-- ═══════════════════════════════════════════════════════════════════
-- PART VI: CONCRETE EXAMPLES
-- ═══════════════════════════════════════════════════════════════════

-- Note: orderOf is noncomputable, so native_decide/decide cannot evaluate it.
-- The period characterization is verified via the period check 10^k % d = 1:

-- Minimal period for divisibility-by-3: k=1 (10^1 % 3 = 1)
example : 10 ^ 1 % 3 = 1 := by native_decide
example (n : ℕ) : 3 ∣ n ↔ 3 ∣ (Nat.digits (10 ^ 1) n).sum :=
  digit_block_rule_of_orderOf_dvd (by norm_num) (by decide)
    1 ((period_iff_orderOf_dvd (by norm_num) 1).mp (by native_decide)) n

-- Minimal period for divisibility-by-7: k=6 (10^6 % 7 = 1)
example : 10 ^ 6 % 7 = 1 := by native_decide

-- Minimal period for divisibility-by-11: k=2 (10^2 % 11 = 1)
example : 10 ^ 2 % 11 = 1 := by native_decide

-- Minimal period for divisibility-by-37: k=3 (10^3 % 37 = 1)
example : 10 ^ 3 % 37 = 1 := by native_decide

-- Base-8 minimal period for divisibility-by-7: k=1 (8^1 % 7 = 1)
example : 8 ^ 1 % 7 = 1 := by native_decide

end DivisibilityRulesOQ01OQ01OQ01
