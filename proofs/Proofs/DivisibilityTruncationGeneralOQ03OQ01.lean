/-
  Divisibility Truncation — Base-b Osculators (OQ-03 → OQ-01)

  Generalizes the base-10 osculator theory of `DivisibilityTruncationGeneralOQ03`
  ("Divisibility Osculators: Bézout Coefficients Are Canonical Osculators") to an
  arbitrary radix b. For any modulus d coprime to b, the Bézout coefficient
  gcdA(b, d) is a canonical osculator — d | b·gcdA(b,d) - 1 — and the truncation
  divisibility test

      d | n  ↔  d | (n / b + c · (n % b))

  holds for any osculator c. This answers OQ-01 of the parent:

    "Generalize to base b: is there an analogous osculator c with d | b·c - 1 for
     any base b coprime to d? The Bézout argument generalizes directly."

  ## Main Results (0 sorries, 0 axioms)

  1. `unified_osculator_base`        — the base-b truncation divisibility test
  2. `bezout_gives_osculator_base`   — gcdA(b,d) is an osculator when gcd(b,d)=1
  3. `osculator_base_exists`         — a canonical osculator in [0,d) always exists
  4. `osculator_base_unique_mod`     — osculators are unique mod d
  5. `canonical_divisibility_test_base` — Bézout → base-b divisibility test pipeline
  6. `recovers_base_ten`             — specializing b=10 recovers the parent's rule
  7. Concrete examples: base-100 (digit-pair) rules for 7, 11, 13, 101;
     hexadecimal (base-16) rules for 3, 5, 17.

  The base-10 development is hard-coded to radix 10 (the digit split n = 10·(n/10)
  + n%10 is baked into its `unified_osculator`); here the radix is a free parameter,
  so the same osculator concept produces divisibility tests in every base at once —
  e.g. hexadecimal digit-sum tests 3 and 5, hexadecimal alternating-digit tests 17,
  and the classical "pairs of decimal digits" tests for 7, 11, 13, 101 in base 100.
-/

import Mathlib.Tactic

namespace DivisibilityTruncationGeneralOQ03OQ01

-- ============================================================
-- PART I: The Base-b Osculator and Divisibility Test
-- ============================================================

/-- `c` is a base-`b` osculator for `d` if `d | b·c - 1` (c is the modular
    inverse of the radix b modulo d). -/
def IsOsculatorBase (b d : ℕ) (c : ℤ) : Prop := (d : ℤ) ∣ (b : ℤ) * c - 1

/-- Digit split in base b: every n decomposes as n = b·(n/b) + (n%b). -/
private lemma div_mod_cast_base (b n : ℕ) :
    (n : ℤ) = (b : ℤ) * ↑(n / b) + ↑(n % b) := by
  have h : b * (n / b) + n % b = n := Nat.div_add_mod n b
  exact_mod_cast h.symm

/-- **The Base-b Unified Osculator Theorem.**

    For any modulus d coprime to the radix b and any osculator c (d | b·c - 1):

      d | n  ↔  d | (n / b + c · (n % b)).

    This is the radix-independent core of the truncation divisibility test: the
    base-10 statement of the parent is the special case b = 10. The proof rests on

      b · (n/b + c·(n%b)) = n + (b·c - 1)·(n%b),

    so when d | (b·c - 1), divisibility transfers across the coprime factor b. -/
theorem unified_osculator_base (b d : ℕ) (c : ℤ) (n : ℕ)
    (hcop : IsCoprime (d : ℤ) (b : ℤ))
    (hc : (d : ℤ) ∣ (b : ℤ) * c - 1) :
    (d : ℤ) ∣ n ↔ (d : ℤ) ∣ (↑(n / b) + c * ↑(n % b)) := by
  have hdiv := div_mod_cast_base b n
  have hkey : (b : ℤ) * (↑(n / b) + c * ↑(n % b))
      = ↑n + ((b : ℤ) * c - 1) * ↑(n % b) := by
    linear_combination -hdiv
  constructor
  · intro hn
    have h1 : (d : ℤ) ∣ ↑n + ((b : ℤ) * c - 1) * ↑(n % b) :=
      dvd_add hn (dvd_mul_of_dvd_left hc _)
    rw [← hkey] at h1
    exact hcop.dvd_of_dvd_mul_left h1
  · intro hq
    have hb : (d : ℤ) ∣ (b : ℤ) * (↑(n / b) + c * ↑(n % b)) :=
      dvd_mul_of_dvd_right hq _
    rw [hkey] at hb
    have hterm : (d : ℤ) ∣ ((b : ℤ) * c - 1) * ↑(n % b) := dvd_mul_of_dvd_left hc _
    have hsub := Int.dvd_sub hb hterm
    simp only [add_sub_cancel_right] at hsub
    exact_mod_cast hsub

-- ============================================================
-- PART II: Bézout Coefficients Give Osculators
-- ============================================================

/-- Bézout identity for the radix: gcd(b,d) = b·gcdA(b,d) + d·gcdB(b,d). -/
theorem bezout_base (b d : ℕ) :
    (Nat.gcd b d : ℤ) = b * Nat.gcdA b d + d * Nat.gcdB b d :=
  Nat.gcd_eq_gcd_ab b d

/-- When gcd(b,d) = 1, gcdA(b,d) is a valid base-b osculator: d | b·gcdA(b,d) - 1. -/
theorem bezout_gives_osculator_base (b d : ℕ) (hcop : Nat.Coprime b d) :
    IsOsculatorBase b d (Nat.gcdA b d) := by
  have hbez := bezout_base b d
  rw [show (Nat.gcd b d : ℤ) = 1 from by exact_mod_cast hcop] at hbez
  exact ⟨-Nat.gcdB b d, by linear_combination -hbez⟩

/-- Bézout → base-b divisibility test, end to end. -/
theorem canonical_divisibility_test_base (b d : ℕ) (n : ℕ) (hcop : Nat.Coprime b d) :
    (d : ℤ) ∣ n ↔ (d : ℤ) ∣ (↑(n / b) + Nat.gcdA b d * ↑(n % b)) :=
  unified_osculator_base b d (Nat.gcdA b d) n hcop.isCoprime.symm
    (bezout_gives_osculator_base b d hcop)

-- ============================================================
-- PART III: Osculator Equivalence Classes
-- ============================================================

/-- If c' ≡ c (mod d) and c is a base-b osculator, so is c'. -/
theorem osculator_base_congr (b d : ℕ) (c c' : ℤ)
    (hc : IsOsculatorBase b d c) (heq : (d : ℤ) ∣ c' - c) :
    IsOsculatorBase b d c' := by
  unfold IsOsculatorBase at *
  have : (b : ℤ) * c' - 1 = ((b : ℤ) * c - 1) + (b : ℤ) * (c' - c) := by ring
  rw [this]; exact dvd_add hc (dvd_mul_of_dvd_right heq (b : ℤ))

/-- Base-b osculators are unique mod d: d | c - c' for any two osculators. -/
theorem osculator_base_unique_mod (b d : ℕ) (hcop : Nat.Coprime b d) (c c' : ℤ)
    (hc : IsOsculatorBase b d c) (hc' : IsOsculatorBase b d c') :
    (d : ℤ) ∣ c - c' := by
  unfold IsOsculatorBase at *
  have hdiff : (d : ℤ) ∣ (b : ℤ) * (c - c') := by
    have : (b : ℤ) * (c - c') = ((b : ℤ) * c - 1) - ((b : ℤ) * c' - 1) := by ring
    rw [this]; exact dvd_sub hc hc'
  exact IsCoprime.dvd_of_dvd_mul_left hcop.isCoprime.symm hdiff

-- ============================================================
-- PART IV: The Canonical Reduced Osculator Exists in [0, d)
-- ============================================================

/-- gcdA(b,d) reduced mod d is still a base-b osculator. -/
theorem osculator_base_mod (b d : ℕ) (_hd : 0 < d) (hcop : Nat.Coprime b d) :
    IsOsculatorBase b d (Nat.gcdA b d % d) := by
  apply osculator_base_congr b d (Nat.gcdA b d) _ (bezout_gives_osculator_base b d hcop)
  refine ⟨-(Nat.gcdA b d / ↑d), ?_⟩
  have h := Int.emod_add_mul_ediv (Nat.gcdA b d) (d : ℤ)
  linarith

/-- A canonical base-b osculator always exists as a natural number in [0, d). -/
theorem osculator_base_exists (b d : ℕ) (hd : 1 < d) (hcop : Nat.Coprime b d) :
    ∃ c : ℕ, c < d ∧ IsOsculatorBase b d c := by
  have hd_pos : 0 < d := Nat.lt_trans Nat.zero_lt_one hd
  have hd_pos_z : (0 : ℤ) < d := by exact_mod_cast hd_pos
  have hd_ne_z : (d : ℤ) ≠ 0 := ne_of_gt hd_pos_z
  set c₀ := Nat.gcdA b d % (d : ℤ) with hc0
  have hnn : 0 ≤ c₀ := Int.emod_nonneg _ hd_ne_z
  have hlt : c₀ < (d : ℤ) := Int.emod_lt_of_pos _ hd_pos_z
  have hosc : IsOsculatorBase b d c₀ := osculator_base_mod b d hd_pos hcop
  refine ⟨c₀.toNat, ?_, ?_⟩
  · have hconv : (c₀.toNat : ℤ) = c₀ := Int.toNat_of_nonneg hnn
    have : (c₀.toNat : ℤ) < (d : ℤ) := by rw [hconv]; exact hlt
    exact_mod_cast this
  · unfold IsOsculatorBase at hosc ⊢
    rw [Int.toNat_of_nonneg hnn]; exact hosc

-- ============================================================
-- PART V: Concrete Examples — Base 100 (pairs of decimal digits)
-- ============================================================

/-- Base 100, d = 7: osculator 4 (100·4 - 1 = 399 = 7·57). -/
theorem osculator_base100_seven : IsOsculatorBase 100 7 4 := by
  unfold IsOsculatorBase; norm_num

/-- 7 | n ↔ 7 | (n/100 + 4·(n%100)) — group the decimal digits in pairs. -/
theorem div_by_seven_base100 (n : ℕ) :
    (7 : ℤ) ∣ n ↔ (7 : ℤ) ∣ (↑(n / 100) + (4 : ℤ) * ↑(n % 100)) :=
  unified_osculator_base 100 7 4 n
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) osculator_base100_seven

/-- Base 100, d = 11: osculator 1 (100·1 - 1 = 99 = 11·9). -/
theorem osculator_base100_eleven : IsOsculatorBase 100 11 1 := by
  unfold IsOsculatorBase; norm_num

/-- 11 | n ↔ 11 | (n/100 + (n%100)) — sum the decimal digit-pairs. -/
theorem div_by_eleven_base100 (n : ℕ) :
    (11 : ℤ) ∣ n ↔ (11 : ℤ) ∣ (↑(n / 100) + (1 : ℤ) * ↑(n % 100)) :=
  unified_osculator_base 100 11 1 n
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) osculator_base100_eleven

/-- Base 100, d = 13: osculator 3 (100·3 - 1 = 299 = 13·23). -/
theorem osculator_base100_thirteen : IsOsculatorBase 100 13 3 := by
  unfold IsOsculatorBase; norm_num

/-- 13 | n ↔ 13 | (n/100 + 3·(n%100)). -/
theorem div_by_thirteen_base100 (n : ℕ) :
    (13 : ℤ) ∣ n ↔ (13 : ℤ) ∣ (↑(n / 100) + (3 : ℤ) * ↑(n % 100)) :=
  unified_osculator_base 100 13 3 n
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) osculator_base100_thirteen

/-- Base 100, d = 101: osculator -1 (100·(-1) - 1 = -101 = 101·(-1)) — the
    base-100 alternating digit-pair rule (101 = 10² + 1). -/
theorem osculator_base100_hundredone : IsOsculatorBase 100 101 (-1) := by
  unfold IsOsculatorBase; norm_num

/-- 101 | n ↔ 101 | (n/100 - (n%100)) — alternate the decimal digit-pairs. -/
theorem div_by_hundredone_base100 (n : ℕ) :
    (101 : ℤ) ∣ n ↔ (101 : ℤ) ∣ (↑(n / 100) + (-1 : ℤ) * ↑(n % 100)) :=
  unified_osculator_base 100 101 (-1) n
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) osculator_base100_hundredone

-- ============================================================
-- PART VI: Concrete Examples — Base 16 (hexadecimal)
-- ============================================================

/-- Hexadecimal, d = 3: osculator 1 (16·1 - 1 = 15 = 3·5) — hex digit-sum tests 3. -/
theorem osculator_base16_three : IsOsculatorBase 16 3 1 := by
  unfold IsOsculatorBase; norm_num

/-- 3 | n ↔ 3 | (n/16 + (n%16)) — sum the hexadecimal digits. -/
theorem div_by_three_base16 (n : ℕ) :
    (3 : ℤ) ∣ n ↔ (3 : ℤ) ∣ (↑(n / 16) + (1 : ℤ) * ↑(n % 16)) :=
  unified_osculator_base 16 3 1 n
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) osculator_base16_three

/-- Hexadecimal, d = 5: osculator 1 (16·1 - 1 = 15 = 5·3) — hex digit-sum tests 5. -/
theorem osculator_base16_five : IsOsculatorBase 16 5 1 := by
  unfold IsOsculatorBase; norm_num

/-- 5 | n ↔ 5 | (n/16 + (n%16)) — sum the hexadecimal digits. -/
theorem div_by_five_base16 (n : ℕ) :
    (5 : ℤ) ∣ n ↔ (5 : ℤ) ∣ (↑(n / 16) + (1 : ℤ) * ↑(n % 16)) :=
  unified_osculator_base 16 5 1 n
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) osculator_base16_five

/-- Hexadecimal, d = 17: osculator -1 (16·(-1) - 1 = -17 = 17·(-1)) — hex
    alternating-digit rule (17 = 16 + 1). -/
theorem osculator_base16_seventeen : IsOsculatorBase 16 17 (-1) := by
  unfold IsOsculatorBase; norm_num

/-- 17 | n ↔ 17 | (n/16 - (n%16)) — alternate the hexadecimal digits. -/
theorem div_by_seventeen_base16 (n : ℕ) :
    (17 : ℤ) ∣ n ↔ (17 : ℤ) ∣ (↑(n / 16) + (-1 : ℤ) * ↑(n % 16)) :=
  unified_osculator_base 16 17 (-1) n
    (by norm_num [Int.isCoprime_iff_gcd_eq_one]) osculator_base16_seventeen

-- ============================================================
-- PART VII: Specialization Recovers the Base-10 Parent
-- ============================================================

/-- Specializing the radix to b = 10 recovers the parent's canonical base-10
    divisibility test, exhibiting the base-10 theory as one instance of the
    radix-free statement. -/
theorem recovers_base_ten (d : ℕ) (n : ℕ) (hcop : Nat.Coprime 10 d) :
    (d : ℤ) ∣ n ↔ (d : ℤ) ∣ (↑(n / 10) + Nat.gcdA 10 d * ↑(n % 10)) :=
  canonical_divisibility_test_base 10 d n hcop

#check @unified_osculator_base
#check @bezout_gives_osculator_base
#check @osculator_base_exists
#check @recovers_base_ten

end DivisibilityTruncationGeneralOQ03OQ01
