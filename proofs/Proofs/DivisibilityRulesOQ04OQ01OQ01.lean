import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

/-
# Parametric block-divisibility rule: both signs, arbitrary block width
  (divisibility-rules-oq-04-oq-01-oq-01)

## Open Question (parent: divisibility-rules-oq-04-oq-01)
"One parametric lemma covering both signs and arbitrary block widths: grouping the
decimal digits into `k`-digit blocks tests every divisor of `10^k − 1` (block sum) or
`10^k + 1` (alternating block sum), recovering the 9/11/99/101/1001/… families
uniformly."

The parent entry `divisibility-rules-oq-04-oq-01` isolated the base-`1000` alternating
block sum as the shared certificate for 7, 11, 13 (because `1001 = 7·11·13 = 10^3 + 1`).
This entry states the fully general phenomenon behind ALL classical decimal
divisibility tests:

* group the digits into blocks of `k` decimal digits, i.e. read `n` in base `10^k`;
* the **block sum** `b₀ + b₁ + b₂ + ⋯` certifies divisibility by every divisor of
  `10^k − 1`, because `10^k ≡ 1`;
* the **alternating block sum** `b₀ − b₁ + b₂ − ⋯` certifies divisibility by every
  divisor of `10^k + 1`, because `10^k ≡ −1`.

Everything factors through one master lemma `dvd_iff_dvd_ofDigits_pow_ten`, a
specialization of Mathlib's base-`b` digit machinery (`Nat.dvd_iff_dvd_ofDigits`)
to base `10^k` with signed evaluation `ε = ±1`. The classical families
(3, 9 | 11 | 9, 11, 33, 99 | 101 | 7, 11, 13) are then one-line corollaries, so the
lone parametric lemma really does subsume every textbook rule and both signs at once.
All results are fully verified (0 sorries, 0 axioms): every step is elementary.
-/

namespace DivisibilityRulesOQ04OQ01OQ01

open Nat

/-- `ofDigits` at the integer base `1` is the (integer) sum of the digit list.
Mathlib's `Nat.ofDigits_one` is stated for the natural-number base; this is the
`ℤ`-coefficient version needed for the signed unification below. -/
theorem ofDigits_one_eq_map_sum (L : List ℕ) :
    Nat.ofDigits (1 : ℤ) L = (L.map fun d : ℕ => (d : ℤ)).sum := by
  induction L with
  | nil => rfl
  | cons d L ih =>
      rw [Nat.ofDigits_one_cons, ih, List.map_cons, List.sum_cons]

/-- The base-`10^k` block sum of `n`: the sum of the `k`-digit decimal blocks of `n`,
read from the least significant. This is the certificate for every divisor of
`10^k − 1`. -/
def blockSum (k n : ℕ) : ℤ :=
  ((Nat.digits (10 ^ k) n).map fun d : ℕ => (d : ℤ)).sum

/-- The base-`10^k` alternating block sum of `n`: `b₀ − b₁ + b₂ − ⋯` over the `k`-digit
decimal blocks. This is the certificate for every divisor of `10^k + 1`. -/
def blockAltSum (k n : ℕ) : ℤ :=
  ((Nat.digits (10 ^ k) n).map fun d : ℕ => (d : ℤ)).alternatingSum

/-- **Master parametric block-divisibility lemma (both signs, any block width).**
For any block width `k`, any signed evaluation `ε : ℤ`, and any modulus `m` with
`m ∣ 10^k − ε`, divisibility of `n` by `m` is detected by the signed base-`10^k`
digit evaluation of `n`. Taking `ε = 1` gives the block-sum tests (divisors of
`10^k − 1`); taking `ε = −1` gives the alternating-block-sum tests (divisors of
`10^k + 1`). -/
theorem dvd_iff_dvd_ofDigits_pow_ten (k : ℕ) (ε : ℤ) (m n : ℕ)
    (hm : (m : ℤ) ∣ (10 : ℤ) ^ k - ε) :
    m ∣ n ↔ (m : ℤ) ∣ Nat.ofDigits ε (Nat.digits (10 ^ k) n) := by
  have h : (m : ℤ) ∣ ((10 ^ k : ℕ) : ℤ) - ε := by
    have hcast : ((10 ^ k : ℕ) : ℤ) = (10 : ℤ) ^ k := by push_cast; ring
    rw [hcast]; exact hm
  exact Nat.dvd_iff_dvd_ofDigits m (10 ^ k) ε h n

/-- **Block-sum test.** If `m ∣ 10^k − 1` then `m ∣ n` iff `m` divides the sum of the
`k`-digit decimal blocks of `n`. Recovers the digit-sum rules (divisors of `10^k − 1`:
3, 9 at `k = 1`; 9, 11, 33, 99 at `k = 2`; …). -/
theorem dvd_iff_dvd_blockSum (k m n : ℕ) (hm : (m : ℤ) ∣ (10 : ℤ) ^ k - 1) :
    m ∣ n ↔ (m : ℤ) ∣ blockSum k n := by
  rw [dvd_iff_dvd_ofDigits_pow_ten k 1 m n hm]
  unfold blockSum
  rw [ofDigits_one_eq_map_sum]

/-- **Alternating-block-sum test.** If `m ∣ 10^k + 1` then `m ∣ n` iff `m` divides the
alternating sum of the `k`-digit decimal blocks of `n`. Recovers the alternating rules
(divisors of `10^k + 1`: 11 at `k = 1`; 101 at `k = 2`; 7, 11, 13 at `k = 3`; …). -/
theorem dvd_iff_dvd_blockAltSum (k m n : ℕ) (hm : (m : ℤ) ∣ (10 : ℤ) ^ k + 1) :
    m ∣ n ↔ (m : ℤ) ∣ blockAltSum k n := by
  have hm' : (m : ℤ) ∣ (10 : ℤ) ^ k - (-1) := by simpa using hm
  rw [dvd_iff_dvd_ofDigits_pow_ten k (-1) m n hm']
  unfold blockAltSum
  rw [Nat.ofDigits_neg_one]

/-- **The unification, packaged.** For every block width `k`, the block sum tests every
divisor of `10^k − 1` and the alternating block sum tests every divisor of `10^k + 1` —
one parametric statement covering both signs and all widths. -/
theorem block_divisibility_families (k m n : ℕ) :
    ((m : ℤ) ∣ (10 : ℤ) ^ k - 1 → (m ∣ n ↔ (m : ℤ) ∣ blockSum k n)) ∧
    ((m : ℤ) ∣ (10 : ℤ) ^ k + 1 → (m ∣ n ↔ (m : ℤ) ∣ blockAltSum k n)) :=
  ⟨fun h => dvd_iff_dvd_blockSum k m n h, fun h => dvd_iff_dvd_blockAltSum k m n h⟩

/-! ### Residue identities (the "why" behind each family) -/

/-- Residue identity behind the block-sum tests: modulo any `m ∣ 10^k − 1`, `n` is
congruent to its base-`10^k` block sum. -/
theorem modEq_blockSum (k m n : ℕ) (hm : (m : ℤ) ∣ (10 : ℤ) ^ k - 1) :
    (n : ℤ) ≡ blockSum k n [ZMOD m] := by
  have h : ((10 ^ k : ℕ) : ℤ) ≡ (1 : ℤ) [ZMOD m] := by
    have hcast : ((10 ^ k : ℕ) : ℤ) = (10 : ℤ) ^ k := by push_cast; ring
    rw [hcast]
    refine Int.modEq_iff_dvd.mpr ?_
    have hneg : (1 : ℤ) - (10 : ℤ) ^ k = -((10 : ℤ) ^ k - 1) := by ring
    rw [hneg]; exact (dvd_neg).mpr hm
  have t := Nat.zmodeq_ofDigits_digits m (10 ^ k) (1 : ℤ) h n
  rw [ofDigits_one_eq_map_sum] at t
  exact t

/-- Residue identity behind the alternating-block-sum tests: modulo any `m ∣ 10^k + 1`,
`n` is congruent to its base-`10^k` alternating block sum. -/
theorem modEq_blockAltSum (k m n : ℕ) (hm : (m : ℤ) ∣ (10 : ℤ) ^ k + 1) :
    (n : ℤ) ≡ blockAltSum k n [ZMOD m] := by
  have h : ((10 ^ k : ℕ) : ℤ) ≡ (-1 : ℤ) [ZMOD m] := by
    have hcast : ((10 ^ k : ℕ) : ℤ) = (10 : ℤ) ^ k := by push_cast; ring
    rw [hcast]
    refine Int.modEq_iff_dvd.mpr ?_
    have hneg : (-1 : ℤ) - (10 : ℤ) ^ k = -((10 : ℤ) ^ k + 1) := by ring
    rw [hneg]; exact (dvd_neg).mpr hm
  have t := Nat.zmodeq_ofDigits_digits m (10 ^ k) (-1 : ℤ) h n
  rw [Nat.ofDigits_neg_one] at t
  exact t

/-! ### Classical families recovered as one-line corollaries

Each rule below is a single instantiation of the master lemma — same proof, different
`(k, ε, m)`. Together they exhibit the "9/11/99/101/1001/…" families uniformly. -/

/-- Divisibility by 3: `k = 1` block sum (digit sum), since `3 ∣ 10 − 1 = 9`. -/
theorem three_dvd_iff (n : ℕ) : 3 ∣ n ↔ (3 : ℤ) ∣ blockSum 1 n :=
  dvd_iff_dvd_blockSum 1 3 n (by norm_num)

/-- Divisibility by 9: `k = 1` block sum (digit sum), since `9 ∣ 10 − 1 = 9`. -/
theorem nine_dvd_iff (n : ℕ) : 9 ∣ n ↔ (9 : ℤ) ∣ blockSum 1 n :=
  dvd_iff_dvd_blockSum 1 9 n (by norm_num)

/-- Divisibility by 11: `k = 1` alternating block sum (alternating digit sum),
since `11 ∣ 10 + 1 = 11`. -/
theorem eleven_dvd_iff (n : ℕ) : 11 ∣ n ↔ (11 : ℤ) ∣ blockAltSum 1 n :=
  dvd_iff_dvd_blockAltSum 1 11 n (by norm_num)

/-- Divisibility by 99: `k = 2` block sum (two-digit blocks), since `99 ∣ 10^2 − 1`. -/
theorem ninetynine_dvd_iff (n : ℕ) : 99 ∣ n ↔ (99 : ℤ) ∣ blockSum 2 n :=
  dvd_iff_dvd_blockSum 2 99 n (by norm_num)

/-- Divisibility by 9 also via the `k = 2` block sum, since `9 ∣ 10^2 − 1 = 99`. -/
theorem nine_dvd_iff_block2 (n : ℕ) : 9 ∣ n ↔ (9 : ℤ) ∣ blockSum 2 n :=
  dvd_iff_dvd_blockSum 2 9 n (by norm_num)

/-- Divisibility by 11 *also* via the `k = 2` block sum, since `11 ∣ 10^2 − 1 = 99`.
Thus 11 admits both an alternating single-digit test and a two-digit block-sum test. -/
theorem eleven_dvd_iff_block2 (n : ℕ) : 11 ∣ n ↔ (11 : ℤ) ∣ blockSum 2 n :=
  dvd_iff_dvd_blockSum 2 11 n (by norm_num)

/-- Divisibility by 101: `k = 2` alternating block sum, since `101 ∣ 10^2 + 1`. -/
theorem hundredone_dvd_iff (n : ℕ) : 101 ∣ n ↔ (101 : ℤ) ∣ blockAltSum 2 n :=
  dvd_iff_dvd_blockAltSum 2 101 n (by norm_num)

/-- Divisibility by 7 (the parent's 7-11-13 rule): `k = 3` alternating block sum,
since `7 ∣ 10^3 + 1 = 1001`. -/
theorem seven_dvd_iff (n : ℕ) : 7 ∣ n ↔ (7 : ℤ) ∣ blockAltSum 3 n :=
  dvd_iff_dvd_blockAltSum 3 7 n (by norm_num)

/-- Divisibility by 11 *also* via the `k = 3` alternating block sum, since
`11 ∣ 10^3 + 1 = 1001`. -/
theorem eleven_dvd_iff_block3 (n : ℕ) : 11 ∣ n ↔ (11 : ℤ) ∣ blockAltSum 3 n :=
  dvd_iff_dvd_blockAltSum 3 11 n (by norm_num)

/-- Divisibility by 13 (the parent's 7-11-13 rule): `k = 3` alternating block sum,
since `13 ∣ 10^3 + 1 = 1001`. -/
theorem thirteen_dvd_iff (n : ℕ) : 13 ∣ n ↔ (13 : ℤ) ∣ blockAltSum 3 n :=
  dvd_iff_dvd_blockAltSum 3 13 n (by norm_num)

end DivisibilityRulesOQ04OQ01OQ01
