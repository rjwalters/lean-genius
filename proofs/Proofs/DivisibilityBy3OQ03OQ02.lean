import Mathlib

/-
# Base-Parametrized Digital Root (OQ-03-OQ-02)

## Open Question

Can Lean 4 formalize a base-parametrized version of all the digital root
results from OQ-03, using the general `Nat.digits b n` with variable b?

For base b ≥ 3, the analog of the digital root formula is:
  dr_b(n) = 1 + ((n - 1) mod (b - 1))    for n > 0
  dr_b(0) = 0

The key property is n ≡ dr_b(n) (mod b-1), which follows from
b ≡ 1 (mod b-1) and Mathlib's `Nat.modEq_digits_sum`.

## Answer: YES — via Nat.modEq_digits_sum

The main ingredients:
- `b % (b-1) = 1` for b ≥ 3 (proved by `Nat.mod_eq_sub_mod`)
- `Nat.modEq_digits_sum (b-1) b hmod n` gives `n ≡ (digits b n).sum [MOD (b-1)]`
- The rest follows from modular arithmetic in Mathlib

## Summary Statistics

- Sorries: 0
- Axioms: 0
- Key Mathlib theorems: `Nat.modEq_digits_sum`, `Nat.dvd_iff_dvd_digits_sum`
-/

namespace DigitalRootBase

open Nat

-- ============================================================================
-- Part I: Key Helper Lemma
-- ============================================================================

/-- For b ≥ 3, b ≡ 1 (mod b-1). Since b = 1 + (b-1), we have b % (b-1) = 1. -/
private lemma base_mod_pred (b : ℕ) (hb : 3 ≤ b) : b % (b - 1) = 1 := by
  rw [Nat.mod_eq_sub_mod (by omega), show b - (b - 1) = 1 from by omega]
  exact Nat.mod_eq_of_lt (by omega)

-- ============================================================================
-- Part II: The Base-b Digital Root Formula
-- ============================================================================

/-- The digital root in base b: `1 + ((n-1) mod (b-1))` for n > 0, 0 for n = 0. -/
def digitalRootBase (b n : ℕ) : ℕ :=
  if n = 0 then 0 else 1 + (n - 1) % (b - 1)

/-- Base case: digital root of 0 is 0. -/
@[simp] theorem digitalRootBase_zero (b : ℕ) : digitalRootBase b 0 = 0 := rfl

/-- For n > 0: digitalRootBase b n = 1 + (n-1) % (b-1). -/
theorem digitalRootBase_pos (b n : ℕ) (hn : 0 < n) :
    digitalRootBase b n = 1 + (n - 1) % (b - 1) := by
  unfold digitalRootBase
  simp only [show n ≠ 0 by omega, ↓reduceIte]

-- ============================================================================
-- Part III: Key Congruence
-- ============================================================================

/-- **Core congruence**: In base b ≥ 3, a number is congruent to
    the sum of its base-b digits modulo (b-1). -/
theorem digitSum_mod_base_pred (b n : ℕ) (hb : 3 ≤ b) :
    n ≡ (Nat.digits b n).sum [MOD (b - 1)] :=
  Nat.modEq_digits_sum (b - 1) b (base_mod_pred b hb) n

/-- n ≡ digitalRootBase b n (mod b-1) for b ≥ 3. -/
theorem congruence (b n : ℕ) (hb : 3 ≤ b) :
    n % (b - 1) = digitalRootBase b n % (b - 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [digitalRootBase]
  · rw [digitalRootBase_pos b n hn]
    -- Rewrite n as (n-1) + 1, then use Nat.add_mod and 1 % (b-1) = 1
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < b - 1)]
    congr 1; ring

-- ============================================================================
-- Part IV: Basic Properties
-- ============================================================================

/-- **Range**: For b ≥ 3 and n > 0, the digital root is between 1 and b-1. -/
theorem digitalRootBase_range (b n : ℕ) (hb : 3 ≤ b) (hn : 0 < n) :
    1 ≤ digitalRootBase b n ∧ digitalRootBase b n ≤ b - 1 := by
  rw [digitalRootBase_pos b n hn]
  constructor
  · omega
  · have h := Nat.mod_lt (n - 1) (show 0 < b - 1 by omega)
    omega

/-- **Single-digit fixed point**: If 1 ≤ n ≤ b-1, then dr_b(n) = n. -/
theorem digitalRootBase_single (b n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ b - 1) :
    digitalRootBase b n = n := by
  rw [digitalRootBase_pos b n (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- **Idempotent**: dr_b(dr_b(n)) = dr_b(n). -/
theorem digitalRootBase_idempotent (b n : ℕ) (hb : 3 ≤ b) :
    digitalRootBase b (digitalRootBase b n) = digitalRootBase b n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [digitalRootBase]
  · have ⟨h1, h2⟩ := digitalRootBase_range b n hb hn
    exact digitalRootBase_single b _ h1 h2

-- ============================================================================
-- Part V: Divisibility
-- ============================================================================

/-- **(b-1) divisibility**: (b-1) | n ↔ dr_b(n) = b-1, for b ≥ 3, n > 0. -/
theorem digitalRootBase_div_pred (b n : ℕ) (hb : 3 ≤ b) (hn : 0 < n) :
    (b - 1) ∣ n ↔ digitalRootBase b n = b - 1 := by
  constructor
  · intro hdvd
    obtain ⟨k, hk⟩ := hdvd
    -- k ≥ 1 since n > 0
    have hk_pos : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with rfl | hpos
      · simp [Nat.mul_zero] at hk; omega
      · exact hpos
    rw [digitalRootBase_pos b n hn]
    -- n-1 = (b-2) + (b-1)*(k-1)
    have hn1 : n - 1 = (b - 2) + (b - 1) * (k - 1) := by omega
    rw [hn1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · intro heq
    rw [Nat.dvd_iff_mod_eq_zero]
    have hcong := congruence b n hb
    rw [heq, Nat.mod_self] at hcong
    exact hcong

/-- **Divisibility via digit sum**: (b-1) | n ↔ (b-1) | (digits b n).sum. -/
theorem div_pred_iff_div_digitSum (b n : ℕ) (hb : 3 ≤ b) :
    (b - 1) ∣ n ↔ (b - 1) ∣ (Nat.digits b n).sum :=
  Nat.dvd_iff_dvd_digits_sum (b - 1) b (base_mod_pred b hb) n

/-- **Factor divisibility rule**: For any divisor d ≥ 2 of (b-1),
    d | n ↔ d | (digits b n).sum. -/
theorem factor_div_rule (b d : ℕ) (hb : 2 ≤ b) (hd : 2 ≤ d) (hdiv : d ∣ (b - 1)) (n : ℕ) :
    d ∣ n ↔ d ∣ (Nat.digits b n).sum := by
  have hmod : b % d = 1 := by
    obtain ⟨k, hk⟩ := hdiv
    have hk_pos : 1 ≤ k := by
      by_contra h; push_neg at h; interval_cases k; omega
    have hb_eq : b = d * k + 1 := by omega
    rw [hb_eq, show d * k + 1 = 1 + d * k from by omega,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  exact Nat.dvd_iff_dvd_digits_sum d b hmod n

-- ============================================================================
-- Part VI: Compatibility with Base-10 (OQ-03)
-- ============================================================================

/-- The base-10 digital root formula from OQ-03 is a special case with b = 10. -/
theorem base10_eq_OQ03_formula (n : ℕ) :
    digitalRootBase 10 n = if n = 0 then 0 else 1 + (n - 1) % 9 := by
  simp [digitalRootBase]

-- ============================================================================
-- Part VII: Concrete Examples
-- ============================================================================

-- Hexadecimal (base 16, b-1 = 15)

/-- In base 16: dr_16(15) = 15 (single digit, fixed point). -/
theorem hex_root_15 : digitalRootBase 16 15 = 15 := by native_decide

/-- In base 16: dr_16(16) = 1 (since 16 ≡ 1 mod 15). -/
theorem hex_root_16 : digitalRootBase 16 16 = 1 := by native_decide

/-- In base 16: dr_16(255) = 15 (since 255 = 17 × 15). -/
theorem hex_root_255 : digitalRootBase 16 255 = 15 := by native_decide

/-- In base 16: 15 | n ↔ 15 | (digits 16 n).sum -/
theorem hex_div15 (n : ℕ) : 15 ∣ n ↔ 15 ∣ (Nat.digits 16 n).sum :=
  div_pred_iff_div_digitSum 16 n (by omega)

-- Octal (base 8, b-1 = 7)

/-- In base 8: dr_8(7) = 7 (single digit). -/
theorem oct_root_7 : digitalRootBase 8 7 = 7 := by native_decide

/-- In base 8: dr_8(64) = 1 (since 64 = 8², and 8 ≡ 1 mod 7). -/
theorem oct_root_64 : digitalRootBase 8 64 = 1 := by native_decide

/-- In base 8: 7 | n ↔ 7 | (digits 8 n).sum -/
theorem oct_div7 (n : ℕ) : 7 ∣ n ↔ 7 ∣ (Nat.digits 8 n).sum :=
  div_pred_iff_div_digitSum 8 n (by omega)

-- Base 7 (b-1 = 6)

/-- In base 7: dr_7(42) = 6 (since 42 = 7 × 6). -/
theorem base7_root_42 : digitalRootBase 7 42 = 6 := by native_decide

/-- In base 7: dr_7(43) = 1 (since 43 ≡ 1 mod 6). -/
theorem base7_root_43 : digitalRootBase 7 43 = 1 := by native_decide

-- ============================================================================
-- Summary Check
-- ============================================================================

#check @digitSum_mod_base_pred
#check @digitalRootBase_idempotent
#check @digitalRootBase_div_pred
#check @factor_div_rule

end DigitalRootBase
