import Mathlib

/-
# The Unified Weighted-Digit Divisibility Framework for General Moduli (OQ-02-OQ-01-OQ-01)

## What This Proves
The parent OQ-02-OQ-01 file proves the **alternating** digit-sum test for `b + 1`
(because `b ≡ -1 (mod b+1)`); its own parent OQ-02 proves the plain **digit-sum** test
for `b - 1` (because `b ≡ 1 (mod b-1)`).  Both are the *same* phenomenon for two special
choices of representative.  This file promotes the principle to **every** modulus `m`:

  For every base `b`, every modulus `m`, and every integer `c` with `b ≡ c (mod m)`,
      n ≡ ofDigits c (digits b n)   (mod m).

The right-hand side is the **weighted digit value** `Σ dᵢ · cⁱ`; choosing `c = b % m`
keeps the weights small, and over `ZMod m` the weights are literally the powers
`(b : ZMod m)ⁱ`, which — because `ZMod m` is finite — form a **periodic weight table**.

## The Unification
| modulus | representative `c` | weights `cⁱ`          | classical test            |
|---------|--------------------|-----------------------|---------------------------|
| `b - 1` | `1`                | `1, 1, 1, …`          | digit sum (parent OQ-02)  |
| `b + 1` | `-1`               | `1, -1, 1, -1, …`     | alternating sum (parent)  |
| `7`  (base 10) | `3`         | `1, 3, 2, 6, 4, 5, …` (period 6) | divisibility by 7 |
| `13` (base 10) | `-3`        | `1,-3,9,-1,3,-9,…` (period 6) | divisibility by 13 |
| `4`  (base 10) | `2`         | `1, 2, 0, 0, …`       | last-two-digits rule      |
| `8`  (base 10) | `2`         | `1, 2, 4, 0, 0, …`    | last-three-digits rule    |

Mathlib provides only the base-10 specializations `Nat.three_dvd_iff`,
`Nat.nine_dvd_iff`, `Nat.eleven_dvd_iff`.  Here `b - 1` and `b + 1` become two lines of
one master theorem, and the genuinely new general-modulus tests (by 7, 13, 4, 8) follow
by supplying a representative.

## Key Mathematical Insight
`n = ofDigits b (digits b n)` exactly, and `ofDigits` is a ring polynomial in the base.
Reducing the base modulo `m` (or pushing into `ZMod m`) therefore reduces `n` to the
weighted digit value with reduced weights — a single application of Mathlib's
`Nat.zmodeq_ofDigits_digits` / `Nat.dvd_iff_dvd_ofDigits`, specialised to an arbitrary
modulus instead of only `b ± 1`.

## Status
- [x] Master congruence `n ≡ ofDigits c (digits b n) (mod m)` for any representative `c`
- [x] Master divisibility rule `m ∣ n ↔ (m:ℤ) ∣ ofDigits c (digits b n)`
- [x] `ZMod m` form: weights are the powers `(b : ZMod m)ⁱ`; `m ∣ n ↔` value `= 0`
- [x] Horner unfolding of the weighted value (general commutative ring base)
- [x] Recovers the digit-sum rule (`c = 1`) and alternating-sum rule (`c = -1`)
- [x] New general-modulus instances: by 7, 13 (period-6 weights), by 4, 8 (prefix tests)
- [x] Periodic weight tables: `(10 : ZMod 7)^6 = 1`, `(10 : ZMod 4)^2 = 0`
- [x] Verified, 0 axioms, 0 sorries, no `native_decide`
-/

namespace DivisibilityBy3OQ02OQ01OQ01

open Nat

-- ============================================================
-- Part 0: A ring-cast lemma for `ofDigits`
-- ============================================================

/-- `ofDigits` commutes with the canonical map `ℕ → R`: casting the natural-number value
    `ofDigits b L` into a commutative ring `R` equals evaluating `ofDigits` with the base
    cast into `R`.  This is what lets us push a number into `ZMod m` (or `ℤ`) and read off
    the weighted digit value with weights `(b : R)ⁱ`. -/
theorem cast_ofDigits {R : Type*} [CommRing R] (b : ℕ) (L : List ℕ) :
    ((Nat.ofDigits b L : ℕ) : R) = Nat.ofDigits (b : R) L := by
  induction L with
  | nil => simp [Nat.ofDigits_eq_foldr]
  | cons d t ih =>
    simp only [Nat.ofDigits_eq_foldr, List.foldr_cons] at *
    push_cast [← ih]; ring

/-- **Horner unfolding.** Over any commutative ring base, the weighted digit value of
    `d :: t` is `d + base · (value of t)`.  Iterating gives `d₀ + c·d₁ + c²·d₂ + ⋯`, i.e.
    digit `i` carries weight `cⁱ`.  (Mathlib's `Nat.ofDigits_cons` is stated only for a
    natural-number base; this is the general-ring companion.) -/
theorem ofDigits_cons_ring {R : Type*} [CommRing R] (c : R) (d : ℕ) (t : List ℕ) :
    Nat.ofDigits c (d :: t) = (d : R) + c * Nat.ofDigits c t := by
  simp [Nat.ofDigits_eq_foldr]

-- ============================================================
-- Part I: The Master Congruence (any modulus, any representative)
-- ============================================================

/-- **The general weighted-digit congruence.**  For every base `b`, modulus `m`, and any
    integer representative `c` of the base (`b ≡ c (mod m)`), the number `n` is congruent
    modulo `m` to the weighted digit value `Σ dᵢ cⁱ = ofDigits c (digits b n)`.
    Taking `c = 1` (modulus `b-1`) gives the digit-sum rule; `c = -1` (modulus `b+1`)
    gives the alternating-sum rule; other `(m, c)` give every other classical test. -/
theorem modEq_ofDigits_repr (m b : ℕ) (c : ℤ) (h : (b : ℤ) ≡ c [ZMOD (m : ℕ)]) (n : ℕ) :
    (n : ℤ) ≡ Nat.ofDigits c (Nat.digits b n) [ZMOD (m : ℕ)] :=
  Nat.zmodeq_ofDigits_digits m b c h n

/-- The same statement using the canonical small representative `c = b % m`.  The weights
    are then `((b % m) : ℤ)ⁱ`, the smallest nonnegative choice. -/
theorem modEq_ofDigits_emod (m b n : ℕ) :
    (n : ℤ) ≡ Nat.ofDigits ((b : ℤ) % (m : ℕ)) (Nat.digits b n) [ZMOD (m : ℕ)] := by
  refine modEq_ofDigits_repr m b _ ?_ n
  show (b : ℤ) % (m : ℕ) = (b : ℤ) % (m : ℕ) % (m : ℕ)
  rw [Int.emod_emod_of_dvd _ dvd_rfl]

-- ============================================================
-- Part II: The Master Divisibility Rule
-- ============================================================

/-- **The general weighted-digit divisibility rule.**  For any base `b`, modulus `m`, and
    representative `c` of the base, `m ∣ n` iff `m` divides the weighted digit value.
    This is Mathlib's `Nat.dvd_iff_dvd_ofDigits` promoted from `b ± 1` to every modulus. -/
theorem dvd_iff_dvd_ofDigits_repr (m b : ℕ) (c : ℤ) (h : (m : ℤ) ∣ (b : ℤ) - c) (n : ℕ) :
    m ∣ n ↔ (m : ℤ) ∣ Nat.ofDigits c (Nat.digits b n) :=
  Nat.dvd_iff_dvd_ofDigits m b c h n

-- ============================================================
-- Part III: The `ZMod m` Form — Weights Are the Powers `(b : ZMod m)ⁱ`
-- ============================================================

/-- **`ZMod m` master form.**  In `ZMod m`, the residue of `n` is the weighted digit value
    whose weight on digit `i` is exactly the power `(b : ZMod m)ⁱ`.  Because `ZMod m` is
    finite, these weights cycle: the weight table is periodic. -/
theorem natCast_eq_ofDigits_zmod (m b n : ℕ) :
    (n : ZMod m) = Nat.ofDigits (b : ZMod m) (Nat.digits b n) := by
  conv_lhs => rw [← Nat.ofDigits_digits b n]
  rw [cast_ofDigits]

/-- **`ZMod m` divisibility rule.**  `m ∣ n` iff the `ZMod m` weighted digit value is `0`. -/
theorem dvd_iff_ofDigits_zmod (m b n : ℕ) :
    m ∣ n ↔ Nat.ofDigits (b : ZMod m) (Nat.digits b n) = 0 := by
  rw [← natCast_eq_ofDigits_zmod]; exact (ZMod.natCast_eq_zero_iff n m).symm

-- ============================================================
-- Part IV: Recovering the Digit-Sum and Alternating-Sum Rules
-- ============================================================

/-- Over `ℤ`, the weighted value with base `1` is the plain integer digit sum. -/
theorem ofDigits_one_int (L : List ℕ) :
    Nat.ofDigits (1 : ℤ) L = (L.map (Nat.cast : ℕ → ℤ)).sum := by
  rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) by norm_num, ← cast_ofDigits, Nat.ofDigits_one]
  push_cast; simp

/-- **Recovers the digit-sum rule (parent OQ-02).**  With representative `c = 1`, modulus
    `b - 1`, the master congruence collapses to `n ≡ Σ dᵢ (mod b-1)`. -/
theorem modEq_digitSum (b n : ℕ) (hb : 2 ≤ b) :
    (n : ℤ) ≡ ((Nat.digits b n).map (Nat.cast : ℕ → ℤ)).sum [ZMOD (b - 1 : ℕ)] := by
  have h : (b : ℤ) ≡ 1 [ZMOD (b - 1 : ℕ)] := by
    rw [Int.modEq_iff_dvd]; refine ⟨-1, ?_⟩
    have : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
    rw [this]; ring
  have := modEq_ofDigits_repr (b - 1) b 1 h n
  rwa [ofDigits_one_int] at this

/-- **Recovers the alternating-sum rule (parent OQ-02-OQ-01).**  With representative
    `c = -1`, modulus `b + 1`, the master congruence collapses to the alternating digit
    sum — exactly the parent's `modEq_altDigitSum`. -/
theorem modEq_altDigitSum (b n : ℕ) :
    (n : ℤ) ≡ ((Nat.digits b n).map (Nat.cast : ℕ → ℤ)).alternatingSum [ZMOD (b + 1 : ℕ)] := by
  have h : (b : ℤ) ≡ -1 [ZMOD (b + 1 : ℕ)] := by
    rw [Int.modEq_iff_dvd]; push_cast; exact ⟨-1, by ring⟩
  have := modEq_ofDigits_repr (b + 1) b (-1) h n
  rwa [Nat.ofDigits_neg_one] at this

-- ============================================================
-- Part V: New General-Modulus Instances (not in Mathlib)
-- ============================================================

/-- **Divisibility by 7 in base 10.**  `7 ∣ n` iff `7 ∣ Σ dᵢ · 3ⁱ`; the weights
    `3ⁱ mod 7 = 1, 3, 2, 6, 4, 5` cycle with period 6.  No base-10 divisibility-by-7
    rule exists in Mathlib. -/
theorem seven_dvd_iff (n : ℕ) :
    7 ∣ n ↔ (7 : ℤ) ∣ Nat.ofDigits (3 : ℤ) (Nat.digits 10 n) :=
  dvd_iff_dvd_ofDigits_repr 7 10 3 (by norm_num) n

/-- **Divisibility by 13 in base 10.**  `13 ∣ n` iff `13 ∣ Σ dᵢ · (-3)ⁱ`; the weights
    `(-3)ⁱ mod 13 = 1, -3, 9, -1, 3, -9` cycle with period 6. -/
theorem thirteen_dvd_iff (n : ℕ) :
    13 ∣ n ↔ (13 : ℤ) ∣ Nat.ofDigits (-3 : ℤ) (Nat.digits 10 n) :=
  dvd_iff_dvd_ofDigits_repr 13 10 (-3) (by norm_num) n

/-- **Divisibility by 4 in base 10 (last-two-digits rule).**  With representative `2`,
    `4 ∣ n` iff `4 ∣ d₀ + 2 d₁` — the weights `2ⁱ mod 4 = 1, 2, 0, 0, …` vanish past the
    first two digits, so only the last two digits matter. -/
theorem four_dvd_iff (n : ℕ) :
    4 ∣ n ↔ (4 : ℤ) ∣ Nat.ofDigits (2 : ℤ) (Nat.digits 10 n) :=
  dvd_iff_dvd_ofDigits_repr 4 10 2 (by norm_num) n

/-- **Divisibility by 8 in base 10 (last-three-digits rule).**  Weights
    `2ⁱ mod 8 = 1, 2, 4, 0, 0, …` vanish past the first three digits. -/
theorem eight_dvd_iff (n : ℕ) :
    8 ∣ n ↔ (8 : ℤ) ∣ Nat.ofDigits (2 : ℤ) (Nat.digits 10 n) :=
  dvd_iff_dvd_ofDigits_repr 8 10 2 (by norm_num) n

/-- Recovering Mathlib's base-10 divisibility-by-9 rule from the framework
    (`c = 1`, modulus `9 = 10 - 1`). -/
theorem nine_dvd_iff (n : ℕ) :
    9 ∣ n ↔ (9 : ℤ) ∣ Nat.ofDigits (1 : ℤ) (Nat.digits 10 n) :=
  dvd_iff_dvd_ofDigits_repr 9 10 1 (by norm_num) n

-- ============================================================
-- Part VI: Periodic Weight Tables
-- ============================================================

/-- The base-10 weights modulo 7 have period 6: `(10 : ZMod 7)^6 = 1`. -/
theorem weight_period_seven : (10 : ZMod 7) ^ 6 = 1 := by decide

/-- The base-10 weights modulo 13 have period 6: `(10 : ZMod 13)^6 = 1`. -/
theorem weight_period_thirteen : (10 : ZMod 13) ^ 6 = 1 := by decide

/-- The base-10 weights modulo 4 vanish past the units and tens place:
    `(10 : ZMod 4)^2 = 0`, the algebraic reason the last-two-digits rule works. -/
theorem weight_vanish_four : (10 : ZMod 4) ^ 2 = 0 := by decide

/-- The base-10 weights modulo 8 vanish past the hundreds place: `(10 : ZMod 8)^3 = 0`. -/
theorem weight_vanish_eight : (10 : ZMod 8) ^ 3 = 0 := by decide

-- ============================================================
-- Part VII: Numerical Verifications (no `native_decide`)
-- ============================================================

/-- `1001 = 7 · 11 · 13`.  Base-10 digits `[1,0,0,1]`, weighted by `3ⁱ`:
    `1 + 0 + 0 + 1·6 = 7`, divisible by 7. -/
example : 7 ∣ 1001 := by
  rw [seven_dvd_iff, show Nat.digits 10 1001 = [1, 0, 0, 1] by simp]; decide

/-- `1234` is not divisible by 7: weighted sum `4 + 3·3 + 2·2 + 1·6 = 23 ≡ 2 (mod 7)`. -/
example : ¬ (7 ∣ 1234) := by
  rw [seven_dvd_iff, show Nat.digits 10 1234 = [4, 3, 2, 1] by simp]; decide

/-- `1001 = 7 · 11 · 13` is divisible by 13: weighted by `(-3)ⁱ`,
    `1 + 0 + 0 + 1·(-1) = 0`. -/
example : 13 ∣ 1001 := by
  rw [thirteen_dvd_iff, show Nat.digits 10 1001 = [1, 0, 0, 1] by simp]; decide

/-- `124` is divisible by 4 (last two digits `24`): weighted by `2ⁱ`, `4 + 2·2 = 8`. -/
example : 4 ∣ 124 := by
  rw [four_dvd_iff, show Nat.digits 10 124 = [4, 2, 1] by simp]; decide

/-- `1000` is divisible by 8 (last three digits `000`): weighted sum `0`. -/
example : 8 ∣ 1000 := by
  rw [eight_dvd_iff, show Nat.digits 10 1000 = [0, 0, 0, 1] by simp]; decide

/-- `123` is not divisible by 8: weighted by `2ⁱ`, `3 + 2·2 + 1·4 = 11 ≡ 3 (mod 8)`. -/
example : ¬ (8 ∣ 123) := by
  rw [eight_dvd_iff, show Nat.digits 10 123 = [3, 2, 1] by simp]; decide

end DivisibilityBy3OQ02OQ01OQ01
