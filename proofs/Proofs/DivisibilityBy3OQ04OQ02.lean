import Mathlib

/-
# Detection Probability for Casting Out Methods

## What This Proves
Formalizes the detection probability of casting-out arithmetic checks:
casting out with modulus d detects exactly (d-1)/d of all single-digit errors.

## Mathematical Model
In base b, a single-digit substitution error at position k changes the value by
δ · b^k, where δ ∈ {-(b-1), ..., -1, 1, ..., (b-1)} is the perturbation amount.

When checking modulo d (where b ≡ 1 mod d), the digit-sum check detects
the error if and only if δ ≢ 0 (mod d), since b^k ≡ 1 (mod d).

For the standard case d = b - 1 (e.g., d = 9 for base 10):
- Perturbation magnitudes range over {1, ..., d}
- Exactly d - 1 are not divisible by d (detected errors)
- Exactly 1 is divisible by d (undetected: the maximal perturbation |δ| = d)
- Detection rate = (d-1)/d

## Status
- [x] Position independence: b^k ≡ 1 (mod d) when b ≡ 1 (mod d)
- [x] Core counting: d-1 of d perturbation magnitudes are detected
- [x] Specialization: casting out nines detects 8/9 of errors
- [x] Specialization: casting out threes detects 2/3 of errors
- [x] Connection to parent framework

## Mathlib Dependencies
- `Nat.pow_mod` : a^k % m = (a % m)^k % m
- `Nat.modEq_digits_sum` : n ≡ (digits b n).sum [MOD d] when b % d = 1
- `Finset.card_Icc` : cardinality of closed intervals
- `ZMod.card` : |ZMod d| = d
-/

namespace DivisibilityBy3OQ04OQ02

open Finset

-- ============================================================
-- Part I: Position Independence of Detection
-- ============================================================

/-- When b ≡ 1 (mod d), all powers b^k ≡ 1 (mod d).
    This means the digit position of an error doesn't affect detectability. -/
theorem base_pow_mod_one (d b : ℕ) (hd : 1 < d) (hb : b % d = 1) (k : ℕ) :
    b ^ k % d = 1 := by
  have h1 : b ^ k % d = (b % d) ^ k % d := Nat.pow_mod b k d
  rw [h1, hb, one_pow, Nat.mod_eq_of_lt hd]

/-- Perturbation residue is position-independent:
    (δ * b^k) % d = δ % d when b ≡ 1 (mod d). -/
theorem perturbation_mod (d b : ℕ) (hd : 1 < d) (hb : b % d = 1) (δ k : ℕ) :
    (δ * b ^ k) % d = δ % d := by
  rw [Nat.mul_mod, base_pow_mod_one d b hd hb k, mul_one]
  exact Nat.mod_mod_of_dvd δ (dvd_refl d)

/-- Divisibility through b^k: d ∣ δ·b^k ↔ d ∣ δ (when b ≡ 1 mod d).
    Detection depends only on the perturbation amount, not position. -/
theorem dvd_mul_pow_iff (d b : ℕ) (hd : 1 < d) (hb : b % d = 1) (δ k : ℕ) :
    d ∣ (δ * b ^ k) ↔ d ∣ δ := by
  constructor
  · intro h
    rw [Nat.dvd_iff_mod_eq_zero] at h ⊢
    rwa [perturbation_mod d b hd hb δ k] at h
  · exact fun h => dvd_mul_of_dvd_left h _

-- ============================================================
-- Part II: Core Counting — Detection Rate
-- ============================================================

/-- In {1, ..., d}, the only multiple of d is d itself. -/
theorem unique_multiple_in_range (d : ℕ) (hd : 0 < d) (n : ℕ)
    (hn_lb : 1 ≤ n) (hn_ub : n ≤ d) (hdvd : d ∣ n) : n = d := by
  obtain ⟨k, rfl⟩ := hdvd
  have hk : k = 1 := by
    have h1 : k ≠ 0 := by intro h; subst h; simp at hn_lb
    have h2 : ¬(2 ≤ k) := by
      intro h
      have := Nat.mul_le_mul_left d h
      linarith
    omega
  subst hk; ring

/-- The multiples of d in {1, ..., d} form the singleton {d}. -/
theorem multiples_in_range (d : ℕ) (hd : 2 ≤ d) :
    (Icc 1 d).filter (fun n => d ∣ n) = {d} := by
  ext n
  simp only [mem_filter, mem_Icc, mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact unique_multiple_in_range d (by omega) n h1 h2 h3
  · rintro rfl
    exact ⟨⟨by omega, le_refl _⟩, dvd_refl _⟩

/-- Exactly 1 perturbation magnitude out of d is undetected (divisible by d). -/
theorem undetected_count (d : ℕ) (hd : 2 ≤ d) :
    ((Icc 1 d).filter (fun n => d ∣ n)).card = 1 := by
  rw [multiples_in_range d hd, card_singleton]

/-- **Detection Rate Theorem**: Exactly d - 1 perturbation magnitudes out of d
    are detected (not divisible by d). Detection probability = (d-1)/d. -/
theorem detected_count (d : ℕ) (hd : 2 ≤ d) :
    ((Icc 1 d).filter (fun n => ¬(d ∣ n))).card = d - 1 := by
  have htotal : (Icc 1 d).card = d := by
    simp only [Nat.card_Icc]; omega
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Icc 1 d) (p := fun n => d ∣ n)
  rw [undetected_count d hd] at hpart
  omega

/-- The detection rate as a ratio: detected × d = (d-1) × total.
    This is the formal statement that the probability equals (d-1)/d. -/
theorem detection_rate_ratio (d : ℕ) (hd : 2 ≤ d) :
    ((Icc 1 d).filter (fun n => ¬(d ∣ n))).card * d =
    (d - 1) * (Icc 1 d).card := by
  have hcard : (Icc 1 d).card = d := by simp only [Nat.card_Icc]; omega
  rw [detected_count d hd, hcard]

-- ============================================================
-- Part III: ZMod Perspective
-- ============================================================

/-- Among the d elements of ZMod d, exactly d - 1 are nonzero (detectable). -/
theorem nonzero_residues_count (d : ℕ) [NeZero d] :
    ((univ : Finset (ZMod d)).erase 0).card = d - 1 := by
  rw [card_erase_of_mem (mem_univ 0), card_univ, ZMod.card d]

-- ============================================================
-- Part IV: Casting Out Nines (d = 9, base 10)
-- ============================================================

/-- **Casting out nines detects 8/9 of single-digit errors.**
    Among perturbation magnitudes {1,...,9}, the 8 values not divisible by 9
    (i.e., {1,2,3,4,5,6,7,8}) are detected. Only |δ| = 9 (digit 0↔9) escapes. -/
theorem nines_detected : ((Icc 1 9).filter (fun n => ¬(9 ∣ n))).card = 8 := by
  native_decide

/-- The undetected error for casting out nines: only |δ| = 9. -/
theorem nines_undetected : ((Icc 1 9).filter (fun n => 9 ∣ n)).card = 1 := by
  native_decide

/-- Total perturbation magnitudes for casting out nines. -/
theorem nines_total : (Icc 1 9).card = 9 := by native_decide

/-- Casting out nines detection rate is 8/9:
    detected × 9 = 8 × total. -/
theorem nines_rate : ((Icc 1 9).filter (fun n => ¬(9 ∣ n))).card * 9 =
    8 * (Icc 1 9).card := by native_decide

-- ============================================================
-- Part V: Casting Out Threes (d = 3)
-- ============================================================

/-- **Casting out threes in base 10**: perturbation magnitudes range over {1,...,9}.
    Multiples of 3 in this range are {3,6,9} — 3 undetected out of 9.
    Detection rate = 6/9 = 2/3. -/
theorem threes_detected_full :
    ((Icc 1 9).filter (fun n => ¬(3 ∣ n))).card = 6 := by native_decide

/-- Threes: 3 of 9 perturbation magnitudes undetected. -/
theorem threes_undetected_full :
    ((Icc 1 9).filter (fun n => 3 ∣ n)).card = 3 := by native_decide

/-- Threes detection rate is 2/3: detected × 3 = 2 × total. -/
theorem threes_rate :
    ((Icc 1 9).filter (fun n => ¬(3 ∣ n))).card * 3 =
    2 * (Icc 1 9).card := by native_decide

/-- **Nines vs Threes**: Casting out nines catches more errors than threes
    (8 vs 6 out of 9 perturbation magnitudes in base 10). -/
theorem nines_better_than_threes :
    ((Icc 1 9).filter (fun n => ¬(9 ∣ n))).card >
    ((Icc 1 9).filter (fun n => ¬(3 ∣ n))).card := by native_decide

-- ============================================================
-- Part VI: Connection to Casting Out Framework
-- ============================================================

/-- For any base b ≥ 3, b ≡ 1 (mod b-1), so casting out with d = b-1 works. -/
theorem casting_out_base_cong (b : ℕ) (hb : 3 ≤ b) : b % (b - 1) = 1 := by
  set m := b - 1
  have hm : 1 < m := by omega
  have hb_eq : b = m + 1 := by omega
  rw [hb_eq, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod,
      Nat.mod_eq_of_lt hm]

/-- Digit-sum perturbation: adding δ·b^k changes the digit sum by δ (mod d). -/
theorem digit_sum_perturbation (d b : ℕ) (hd : 1 < d) (hb : b % d = 1) (x δ k : ℕ) :
    (x + δ * b ^ k) ≡ x + δ [MOD d] := by
  show (x + δ * b ^ k) % d = (x + δ) % d
  rw [Nat.add_mod, perturbation_mod d b hd hb δ k, ← Nat.add_mod]

-- ============================================================
-- Part VII: Concrete Examples
-- ============================================================

/-- The OQ-04 limitation (579 vs 588, differing by 9) is the undetected case. -/
example : 9 ∣ (588 - 579) := by norm_num

/-- An error of magnitude 1 IS detected. -/
example : ¬(9 ∣ (580 - 579)) := by norm_num

/-- All magnitudes 1-8 are detected by casting out nines. -/
example : ∀ δ ∈ ({1, 2, 3, 4, 5, 6, 7, 8} : Finset ℕ), ¬(9 ∣ δ) := by decide

/-- The sole undetected magnitude: 9. -/
example : 9 ∣ 9 := dvd_refl 9

-- ============================================================
-- Part VIII: Other Bases
-- ============================================================

/-- Casting out sevens in octal (b = 8, d = 7): detects 6/7 of errors. -/
theorem octal_detected : ((Icc 1 7).filter (fun n => ¬(7 ∣ n))).card = 6 := by
  native_decide

/-- Casting out fifteens in hex (b = 16, d = 15): detects 14/15 of errors. -/
theorem hex_detected : ((Icc 1 15).filter (fun n => ¬(15 ∣ n))).card = 14 := by
  native_decide

/-- Binary check (b = 2, d = 1): trivially detects nothing since every integer
    is divisible by 1. This confirms d ≥ 2 is needed. -/
theorem binary_trivial : ((Icc 1 1).filter (fun n => ¬(1 ∣ n))).card = 0 := by
  native_decide

end DivisibilityBy3OQ04OQ02
