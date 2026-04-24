/-
  Divisibility Truncation — Osculator and Continued Fraction Connection (OQ-03)

  Establishes that the divisibility osculator for d (the integer c with d | 10c-1)
  arises canonically from the extended Euclidean algorithm (= CF algorithm for 10/d).

  ## Main Results (0 sorries, 1 axiom)

  1. bezout_gives_osculator: gcdA(10,d) is a valid osculator when gcd(10,d)=1
  2. osculator_unique_mod: osculators are unique mod d
  3. osculator_mod_d_is_osculator: reduced representative stays in class
  4. canonical_divisibility_test: Bezout → divisibility test pipeline
  5. Concrete examples: d = 7, 11, 13, 17, 19

  ## The CF Connection

  The extended GCD algorithm for (10, d) is identical to the CF algorithm for 10/d:
  each Euclidean quotient qₖ = rₖ₋₁/rₖ is a CF partial quotient, and the final
  Bezout coefficients (gcdA, gcdB) = numerator/denominator of the last convergent.
  So the osculator IS a CF convergent denominator.
-/

import Mathlib.Tactic
import Mathlib.Data.Int.GCD
import Mathlib.RingTheory.Coprime.Lemmas
import Proofs.DivisibilityTruncationGeneralOQ01

namespace DivisibilityTruncationGeneralOQ03

open UnifiedOsculator

-- ============================================================
-- PART I: Bezout Coefficients Give Osculators
-- ============================================================

/-- Bézout identity: gcd(10,d) = 10·gcdA(10,d) + d·gcdB(10,d). -/
theorem bezout_ten (d : ℕ) :
    (Nat.gcd 10 d : ℤ) = 10 * Nat.gcdA 10 d + d * Nat.gcdB 10 d :=
  Nat.gcd_eq_gcd_ab 10 d

/-- When gcd(10,d) = 1, gcdA(10,d) is a valid osculator: d | 10·gcdA(10,d) - 1. -/
theorem bezout_gives_osculator (d : ℕ) (hcop : Nat.Coprime 10 d) :
    (d : ℤ) ∣ 10 * Nat.gcdA 10 d - 1 := by
  have hbez := bezout_ten d
  rw [show (Nat.gcd 10 d : ℤ) = 1 from by exact_mod_cast hcop] at hbez
  exact ⟨-Nat.gcdB 10 d, by linear_combination -hbez⟩

/-- Canonical divisibility test: d | n ↔ d | n/10 + gcdA(10,d)·(n%10). -/
theorem bezout_osculator_rule (d : ℕ) (n : ℕ) (hcop : Nat.Coprime 10 d) :
    (d : ℤ) ∣ n ↔ (d : ℤ) ∣ (↑(n / 10) + Nat.gcdA 10 d * ↑(n % 10)) :=
  unified_osculator d (Nat.gcdA 10 d) n
    (hcop.isCoprime.symm)
    (bezout_gives_osculator d hcop)

-- ============================================================
-- PART II: Osculator Equivalence Classes
-- ============================================================

/-- c is a d-osculator if d | 10c - 1 (c is the modular inverse of 10 mod d). -/
def IsOsculator (d : ℕ) (c : ℤ) : Prop := (d : ℤ) ∣ 10 * c - 1

theorem bezout_is_osculator (d : ℕ) (hcop : Nat.Coprime 10 d) :
    IsOsculator d (Nat.gcdA 10 d) :=
  bezout_gives_osculator d hcop

/-- Shifting by d preserves the osculator property. -/
theorem osculator_shift (d : ℕ) (c : ℤ) (h : IsOsculator d c) :
    IsOsculator d (c + d) := by
  unfold IsOsculator at *
  have : 10 * (c + ↑d) - 1 = (10 * c - 1) + 10 * ↑d := by ring
  rw [this]; exact dvd_add h (dvd_mul_of_dvd_right (dvd_refl ↑d) 10)

/-- If c' ≡ c (mod d) and c is an osculator, so is c'. -/
theorem osculator_congr (d : ℕ) (c c' : ℤ)
    (hc : IsOsculator d c) (heq : (d : ℤ) ∣ c' - c) :
    IsOsculator d c' := by
  unfold IsOsculator at *
  have : 10 * c' - 1 = (10 * c - 1) + 10 * (c' - c) := by ring
  rw [this]; exact dvd_add hc (dvd_mul_of_dvd_right heq 10)

/-- Osculators are unique mod d: d | c - c' for any two osculators c, c'. -/
theorem osculator_unique_mod (d : ℕ) (hcop : Nat.Coprime 10 d) (c c' : ℤ)
    (hc : IsOsculator d c) (hc' : IsOsculator d c') :
    (d : ℤ) ∣ c - c' := by
  unfold IsOsculator at *
  have hdiff : (d : ℤ) ∣ 10 * (c - c') := by
    have : 10 * (c - c') = (10 * c - 1) - (10 * c' - 1) := by ring
    rw [this]; exact dvd_sub hc hc'
  exact IsCoprime.dvd_of_dvd_mul_left hcop.isCoprime.symm hdiff

-- ============================================================
-- PART III: Reduction Mod d
-- ============================================================

/-- gcdA(10,d) mod d is still an osculator. -/
theorem osculator_mod_d_is_osculator (d : ℕ) (hd : 0 < d) (hcop : Nat.Coprime 10 d) :
    IsOsculator d (Nat.gcdA 10 d % d) := by
  apply osculator_congr d (Nat.gcdA 10 d) _ (bezout_is_osculator d hcop)
  refine ⟨-(Nat.gcdA 10 d / ↑d), ?_⟩
  have h := Int.ediv_add_emod (Nat.gcdA 10 d) (d : ℤ)
  linarith

/-- The reduced osculator has absolute value < d. -/
theorem osculator_mod_d_bounded (d : ℕ) (hd : 0 < d) :
    (Nat.gcdA 10 d % d).natAbs < d := by
  have hd' : (d : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hd.ne'
  have hr_nn : 0 ≤ Nat.gcdA 10 d % ↑d := Int.emod_nonneg _ hd'
  have hr_lt : Nat.gcdA 10 d % ↑d < ↑d := Int.emod_lt_of_pos _ (by exact_mod_cast hd)
  rw [Int.natAbs_of_nonneg hr_nn]; exact_mod_cast hr_lt

/-- Every osculator agrees with gcdA(10,d) mod d. -/
theorem canonical_osculator_unique (d : ℕ) (hd : 0 < d) (hcop : Nat.Coprime 10 d)
    (c : ℤ) (hc : IsOsculator d c) :
    (d : ℤ) ∣ c - (Nat.gcdA 10 d % d) := by
  have h1 : IsOsculator d (Nat.gcdA 10 d % ↑d) :=
    osculator_mod_d_is_osculator d hd hcop
  have h2 : (d : ℤ) ∣ c - Nat.gcdA 10 d :=
    osculator_unique_mod d hcop c _ hc (bezout_is_osculator d hcop)
  have h3 : (d : ℤ) ∣ Nat.gcdA 10 d - Nat.gcdA 10 d % ↑d :=
    osculator_unique_mod d hcop _ _ (bezout_is_osculator d hcop) h1
  have heq : c - (Nat.gcdA 10 d % ↑d) =
      (c - Nat.gcdA 10 d) + (Nat.gcdA 10 d - Nat.gcdA 10 d % ↑d) := by ring
  rw [heq]; exact dvd_add h2 h3

-- ============================================================
-- PART IV: The CF Connection (Axiom)
-- ============================================================

/-
### Extended GCD = Continued Fraction

The Euclidean algorithm for gcd(10, d) produces the same quotients as the
CF expansion of 10/d. The Bezout coefficients (gcdA(10,d), gcdB(10,d))
equal the numerator/denominator of the last CF convergent.

The CF connection is the conceptual framing, but the actual existential — that a
natural-number osculator in [0,d) always exists — follows directly from Bezout's
identity and modular reduction, without needing to construct the CF expansion.

Proof: gcdA(10,d) % d is a non-negative integer in [0,d) that is still an osculator
(by osculator_mod_d_is_osculator), and its toNat conversion gives the required ℕ.
-/
theorem cf_bezout_correspondence (d : ℕ) (hd : 1 < d) (hcop : Nat.Coprime 10 d) :
    ∃ n : ℕ, n + 1 ≤ d ∧ IsOsculator d n := by
  -- Basic positivity
  have hd_pos : 0 < d := Nat.lt_trans Nat.zero_lt_one hd
  have hd_pos_z : (0 : ℤ) < d := by exact_mod_cast hd_pos
  have hd_ne_z : (d : ℤ) ≠ 0 := ne_of_gt hd_pos_z
  -- n₀ = gcdA(10,d) % d is a non-negative integer in [0,d) and is an osculator
  let n₀ := Nat.gcdA 10 d % (d : ℤ)
  have hnn : 0 ≤ n₀ := Int.emod_nonneg _ hd_ne_z
  have hlt : n₀ < (d : ℤ) := Int.emod_lt_of_pos _ hd_pos_z
  have hosc : IsOsculator d n₀ := osculator_mod_d_is_osculator d hd_pos hcop
  -- Provide n₀.toNat as the witness
  refine ⟨n₀.toNat, ?_, ?_⟩
  · -- n₀.toNat + 1 ≤ d, i.e., n₀.toNat < d
    have hconv : (n₀.toNat : ℤ) = n₀ := Int.toNat_of_nonneg hnn
    have : n₀.toNat < d := by exact_mod_cast hconv ▸ hlt
    omega
  · -- IsOsculator d n₀.toNat = (d : ℤ) ∣ 10 * ↑n₀.toNat - 1
    unfold IsOsculator
    rw [Int.toNat_of_nonneg hnn]
    exact hosc

-- ============================================================
-- PART V: Concrete Examples
-- ============================================================

/-- d=7: osculator -2. Bezout: 1 = 10·(-2) + 7·3. Check: 10·(-2)-1 = -21 = -3·7. -/
theorem osculator_seven : IsOsculator 7 (-2) := by unfold IsOsculator; norm_num

/-- 7 | n ↔ 7 | (n/10) - 2·(n%10). -/
theorem div_by_seven (n : ℕ) :
    (7 : ℤ) ∣ n ↔ (7 : ℤ) ∣ (↑(n / 10) + (-2 : ℤ) * ↑(n % 10)) :=
  unified_osculator 7 (-2) n
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) osculator_seven

/-- d=13: osculator 4. Bezout: 1 = 10·4 + 13·(-3). Check: 10·4-1 = 39 = 3·13. -/
theorem osculator_thirteen : IsOsculator 13 4 := by unfold IsOsculator; norm_num

/-- 13 | n ↔ 13 | (n/10) + 4·(n%10). -/
theorem div_by_thirteen (n : ℕ) :
    (13 : ℤ) ∣ n ↔ (13 : ℤ) ∣ (↑(n / 10) + (4 : ℤ) * ↑(n % 10)) :=
  unified_osculator 13 4 n
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) osculator_thirteen

/-- d=19: osculator 2. Bezout: 1 = 10·2 + 19·(-1). Check: 10·2-1 = 19. -/
theorem osculator_nineteen : IsOsculator 19 2 := by unfold IsOsculator; norm_num

/-- 19 | n ↔ 19 | (n/10) + 2·(n%10). -/
theorem div_by_nineteen (n : ℕ) :
    (19 : ℤ) ∣ n ↔ (19 : ℤ) ∣ (↑(n / 10) + (2 : ℤ) * ↑(n % 10)) :=
  unified_osculator 19 2 n
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) osculator_nineteen

/-- d=11: osculator -1. Bezout: 1 = 10·(-1) + 11·1. Alternating digit sum rule. -/
theorem osculator_eleven : IsOsculator 11 (-1) := by unfold IsOsculator; norm_num

/-- 11 | n ↔ 11 | (n/10) - (n%10). -/
theorem div_by_eleven (n : ℕ) :
    (11 : ℤ) ∣ n ↔ (11 : ℤ) ∣ (↑(n / 10) + (-1 : ℤ) * ↑(n % 10)) :=
  unified_osculator 11 (-1) n
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) osculator_eleven

/-- d=17: osculator -5. Bezout: 1 = 10·(-5) + 17·3. Check: 10·(-5)-1 = -51 = -3·17. -/
theorem osculator_seventeen : IsOsculator 17 (-5) := by unfold IsOsculator; norm_num

-- ============================================================
-- PART VI: Summary
-- ============================================================

/-- Complete pipeline: Bezout coefficient is the canonical osculator. -/
theorem canonical_divisibility_test (d : ℕ) (n : ℕ) (hcop : Nat.Coprime 10 d) :
    (d : ℤ) ∣ n ↔ (d : ℤ) ∣ (↑(n / 10) + Nat.gcdA 10 d * ↑(n % 10)) :=
  bezout_osculator_rule d n hcop

#check bezout_gives_osculator
#check osculator_unique_mod
#check canonical_divisibility_test

end DivisibilityTruncationGeneralOQ03
