import Mathlib

/-
# Divisibility By Three OQ-01 → OQ-03: Casting Out Nines, Generalized

## Open question

`divisibility-by-three-oq-01-oq-03`: *Casting out nines, generalized —
the base-`b` digit sum is congruent to `n` modulo `d` whenever the base
satisfies `b ≡ 1 (mod d)`.*

The classical "casting out nines" rule states that a natural number `n` is
congruent, modulo `9`, to the sum of its decimal digits; the "casting out
threes" rule is the same statement modulo `3`.  Both are the special case
`b = 10`, `d ∈ {3, 9}` of a single phenomenon: the digit-sum test works in
base `b` for a modulus `d` exactly when `b ≡ 1 (mod d)`, i.e. when
`d ∣ (b - 1)`.

The parent entry `divisibility-by-three-oq-01` develops digital-root theory
in base `10`; the sibling `divisibility-by-three-oq-01-oq-02` gives a base-`10`
osculator for divisors coprime to `10`.  Both are anchored to base `10`.
This entry removes the base restriction entirely.

Mathlib provides the base-agnostic congruence `Nat.modEq_digits_sum` and the
signed master lemma `Nat.dvd_iff_dvd_ofDigits`, but only *instantiates* them at
base `10` (`Nat.three_dvd_iff`, `Nat.nine_dvd_iff`, `Nat.eleven_dvd_iff`).
Here we package the two genuinely general statements and exhibit them at bases
that Mathlib never touches.

## What this file proves (0 axioms, 0 sorries)

* `digitSum_modEq` — `b ≡ 1 (mod d) → n ≡ (digits b n).sum (mod d)`
  (the congruence form; a thin repackage of `Nat.modEq_digits_sum`).
* `dvd_iff_dvd_digitSum` — the **divisibility test** in signed form:
  `(d : ℤ) ∣ (b - 1) → (d ∣ n ↔ d ∣ (digits b n).sum)`.
* `digitSum_test_of_dvd_pred` — the **headline**: for every base `b ≥ 1` and
  every divisor `d` of `b - 1`, `d ∣ n ↔ d ∣ (digits b n).sum`.  This single
  statement subsumes every classical "casting out" rule.
* `dvd_iff_dvd_alternatingSum` — the dual **alternating-sum test**:
  `(d : ℤ) ∣ (b + 1) → (d ∣ n ↔ (d : ℤ) ∣ alternatingSum (digits b n))`.
  This generalizes divisibility-by-eleven from base `10` to every base.
* Concrete instances Mathlib does not have: casting out fifteens (and threes,
  fives) in hexadecimal, casting out elevens in base `12`, alternating
  seventeens in hexadecimal, together with the base-`10` classics recovered as
  corollaries of the general theorems.
-/

namespace DivisibilityBy3OQ01OQ03

open Nat

/-! ## The general digit-sum test (base `b ≡ 1 (mod d)`) -/

/-- **Generalized casting out nines (congruence form).**  If the base `b` is
congruent to `1` modulo `d`, then any `n` is congruent modulo `d` to the sum of
its base-`b` digits.  Base `10`, `d = 9` is the classical rule. -/
theorem digitSum_modEq (b d n : ℕ) (h : b % d = 1) :
    n ≡ (Nat.digits b n).sum [MOD d] :=
  Nat.modEq_digits_sum d b h n

/-- **Generalized casting out nines (divisibility form).**  When
`(d : ℤ) ∣ b - 1`, divisibility of `n` by `d` is equivalent to divisibility of
its base-`b` digit sum by `d`.  Signed hypothesis so that the trivial modulus
`d = 1` and arbitrarily large bases are covered uniformly. -/
theorem dvd_iff_dvd_digitSum (b d n : ℕ) (h : (d : ℤ) ∣ (b : ℤ) - 1) :
    d ∣ n ↔ d ∣ (Nat.digits b n).sum := by
  have t := Nat.dvd_iff_dvd_ofDigits d b (1 : ℤ) h n
  have e : Nat.ofDigits (1 : ℤ) (Nat.digits b n) = ((Nat.digits b n).sum : ℤ) := by
    have h' := Nat.coe_ofDigits ℤ 1 (Nat.digits b n)
    rw [Nat.ofDigits_one, Nat.cast_one] at h'
    exact h'.symm
  rw [e, Int.natCast_dvd_natCast] at t
  exact t

/-- **Headline: every divisor of `b - 1` admits a base-`b` digit-sum test.**
For any base `b ≥ 1` and any `d ∣ (b - 1)`, `n` is divisible by `d` iff the sum
of its base-`b` digits is.  Recovers casting out nines/threes (base `10`),
casting out fifteens (base `16`), casting out elevens (base `12`), … all at
once. -/
theorem digitSum_test_of_dvd_pred (b d n : ℕ) (hb : 1 ≤ b) (hd : d ∣ b - 1) :
    d ∣ n ↔ d ∣ (Nat.digits b n).sum := by
  apply dvd_iff_dvd_digitSum
  have hcast : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by
    rw [Nat.cast_sub hb, Nat.cast_one]
  rw [← hcast]
  exact_mod_cast hd

/-! ## The dual alternating-sum test (base `b ≡ -1 (mod d)`) -/

/-- **Generalized casting out elevens (alternating divisibility form).**  When
`(d : ℤ) ∣ b + 1`, divisibility of `n` by `d` is equivalent to divisibility of
the alternating sum of its base-`b` digits.  Base `10`, `d = 11` is the
classical alternating rule; base `16`, `d = 17` is a new instance. -/
theorem dvd_iff_dvd_alternatingSum (b d n : ℕ) (h : (d : ℤ) ∣ (b : ℤ) + 1) :
    d ∣ n ↔ (d : ℤ) ∣ ((Nat.digits b n).map fun x : ℕ => (x : ℤ)).alternatingSum := by
  have hc : (d : ℤ) ∣ (b : ℤ) - (-1) := by rwa [sub_neg_eq_add]
  have t := Nat.dvd_iff_dvd_ofDigits d b (-1 : ℤ) hc n
  rwa [Nat.ofDigits_neg_one] at t

/-! ## Classical base-`10` rules, recovered as corollaries -/

/-- Casting out nines (base `10`), as an instance of the general test. -/
theorem nine_dvd_iff (n : ℕ) : 9 ∣ n ↔ 9 ∣ (Nat.digits 10 n).sum :=
  dvd_iff_dvd_digitSum 10 9 n (by norm_num)

/-- Casting out threes (base `10`), as an instance of the general test. -/
theorem three_dvd_iff (n : ℕ) : 3 ∣ n ↔ 3 ∣ (Nat.digits 10 n).sum :=
  dvd_iff_dvd_digitSum 10 3 n (by norm_num)

/-- Casting out elevens (base `10`, alternating), recovering `Nat.eleven_dvd_iff`. -/
theorem eleven_dvd_iff (n : ℕ) :
    11 ∣ n ↔ (11 : ℤ) ∣ ((Nat.digits 10 n).map fun x : ℕ => (x : ℤ)).alternatingSum :=
  dvd_iff_dvd_alternatingSum 10 11 n (by norm_num)

/-! ## New instances beyond base `10` -/

/-- **Casting out fifteens in hexadecimal.**  `15 ∣ n` iff `15` divides the sum
of the base-`16` digits of `n`. -/
theorem hex_fifteen_dvd_iff (n : ℕ) : 15 ∣ n ↔ 15 ∣ (Nat.digits 16 n).sum :=
  dvd_iff_dvd_digitSum 16 15 n (by norm_num)

/-- Casting out threes in hexadecimal (`3 ∣ 16 - 1`). -/
theorem hex_three_dvd_iff (n : ℕ) : 3 ∣ n ↔ 3 ∣ (Nat.digits 16 n).sum :=
  dvd_iff_dvd_digitSum 16 3 n (by norm_num)

/-- Casting out fives in hexadecimal (`5 ∣ 16 - 1`). -/
theorem hex_five_dvd_iff (n : ℕ) : 5 ∣ n ↔ 5 ∣ (Nat.digits 16 n).sum :=
  dvd_iff_dvd_digitSum 16 5 n (by norm_num)

/-- **Casting out elevens in base twelve** (duodecimal): `11 ∣ n` iff `11`
divides the sum of the base-`12` digits of `n`. -/
theorem duodecimal_eleven_dvd_iff (n : ℕ) : 11 ∣ n ↔ 11 ∣ (Nat.digits 12 n).sum :=
  dvd_iff_dvd_digitSum 12 11 n (by norm_num)

/-- **Alternating seventeens in hexadecimal** (`17 ∣ 16 + 1`): `17 ∣ n` iff `17`
divides the alternating sum of the base-`16` digits of `n`. -/
theorem hex_seventeen_alternating_dvd_iff (n : ℕ) :
    17 ∣ n ↔ (17 : ℤ) ∣ ((Nat.digits 16 n).map fun x : ℕ => (x : ℤ)).alternatingSum :=
  dvd_iff_dvd_alternatingSum 16 17 n (by norm_num)

/-- **Alternating sevens in base six**: `7 ∣ 6 + 1`, so `7 ∣ n` iff `7` divides
the alternating sum of the base-`6` digits. -/
theorem base6_seven_alternating_dvd_iff (n : ℕ) :
    7 ∣ n ↔ (7 : ℤ) ∣ ((Nat.digits 6 n).map fun x : ℕ => (x : ℤ)).alternatingSum :=
  dvd_iff_dvd_alternatingSum 6 7 n (by norm_num)

end DivisibilityBy3OQ01OQ03
