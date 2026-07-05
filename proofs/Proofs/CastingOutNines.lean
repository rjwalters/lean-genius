/-
Casting Out Nines: Digit-Sum Congruences and the Multiplicative Check

Source: Open question from the casting-out-nines gallery entry
Status: VERIFIED (0 axioms, 0 sorries)

"Casting out nines" is the classical hand-computation error check. Its
mathematical basis is that the decimal digit sum S(n) of a natural number is
congruent to n itself modulo 9, and that this congruence is compatible with
both addition and multiplication. Concretely, to sanity-check a product
a · b = c one verifies S(a) · S(b) ≡ S(c) (mod 9); a mismatch certifies an
arithmetic error.

This file assembles the elementary theory:

  * The base-agnostic congruence  n ≡ (digits b' n).sum (mod b)  whenever
    b' ≡ 1 (mod b), via `Nat.modEq_digits_sum`.
  * The mod-9 and mod-3 congruences, and the resulting divisibility rules
    packaged as `↔` statements on the digit sum.
  * The additive and multiplicative compatibility laws — the actual justification
    of the casting-out-nines check — S(a+b) ≡ S(a)+S(b) and
    S(a·b) ≡ S(a)·S(b) modulo 9, together with a soundness statement for the
    multiplication check.
  * The alternating-digit-sum divisibility rule for 11.
  * Worked numerical instances that require no digit computation.

Everything reduces to Mathlib's `Nat.modEq_*_digits_sum` congruences; the
content surfaced here is packaging them as usable divisibility criteria plus
the compatibility laws that make the check sound.
-/

import Mathlib

namespace CastingOutNines

/-! ## Digit sum -/

/-- The decimal digit sum of `n`. -/
def S (n : ℕ) : ℕ := (Nat.digits 10 n).sum

/-! ## Part I: The base-agnostic congruence

For any base `b'` congruent to `1` modulo `b`, a number is congruent to its
base-`b'` digit sum modulo `b`. Taking `b = 9, 3` and `b' = 10` (since
`10 ≡ 1 (mod 9)` and `10 ≡ 1 (mod 3)`) recovers the classical rules. -/

/-- Base-agnostic form: `n ≡ (digits b' n).sum (mod b)` when `b' ≡ 1 (mod b)`. -/
theorem modEq_digitSum_base (b b' : ℕ) (h : b' % b = 1) (n : ℕ) :
    n ≡ (Nat.digits b' n).sum [MOD b] :=
  Nat.modEq_digits_sum b b' h n

/-- `n ≡ S(n) (mod 9)`: the core casting-out-nines congruence. -/
theorem modEq_nine (n : ℕ) : n ≡ S n [MOD 9] :=
  Nat.modEq_nine_digits_sum n

/-- `n ≡ S(n) (mod 3)`: the digit-sum rule for divisibility by three. -/
theorem modEq_three (n : ℕ) : n ≡ S n [MOD 3] :=
  Nat.modEq_three_digits_sum n

/-! ## Part II: Divisibility rules

The congruences of Part I turn into `↔` divisibility criteria on the digit
sum. -/

/-- **Divisibility rule for 9.** `n` is divisible by 9 iff its digit sum is. -/
theorem nine_dvd_iff (n : ℕ) : 9 ∣ n ↔ 9 ∣ S n := by
  rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
  exact ⟨(modEq_nine n).symm.trans, (modEq_nine n).trans⟩

/-- **Divisibility rule for 3.** `n` is divisible by 3 iff its digit sum is. -/
theorem three_dvd_iff (n : ℕ) : 3 ∣ n ↔ 3 ∣ S n := by
  rw [← Nat.modEq_zero_iff_dvd, ← Nat.modEq_zero_iff_dvd]
  exact ⟨(modEq_three n).symm.trans, (modEq_three n).trans⟩

/-! ## Part III: Compatibility laws — the check itself

The digit sum is a mod-9 homomorphism for both `+` and `·`. These are the
laws that make the casting-out-nines check sound: they say that reducing to
digit sums before adding/multiplying does not change the residue mod 9. -/

/-- Digit sum is additive modulo 9: `S(a + b) ≡ S(a) + S(b) (mod 9)`. -/
theorem digitSum_add (a b : ℕ) : S (a + b) ≡ S a + S b [MOD 9] :=
  calc S (a + b) ≡ a + b [MOD 9] := (modEq_nine (a + b)).symm
    _ ≡ S a + S b [MOD 9] := (modEq_nine a).add (modEq_nine b)

/-- Digit sum is multiplicative modulo 9: `S(a · b) ≡ S(a) · S(b) (mod 9)`. -/
theorem digitSum_mul (a b : ℕ) : S (a * b) ≡ S a * S b [MOD 9] :=
  calc S (a * b) ≡ a * b [MOD 9] := (modEq_nine (a * b)).symm
    _ ≡ S a * S b [MOD 9] := (modEq_nine a).mul (modEq_nine b)

/-- **Soundness of the multiplication check.** If `a · b = c` then the digit
sums satisfy `S(a) · S(b) ≡ S(c) (mod 9)`. Contrapositively, a failure of this
congruence proves that `a · b ≠ c` — this is exactly casting out nines. -/
theorem check_mul (a b c : ℕ) (h : a * b = c) : S a * S b ≡ S c [MOD 9] := by
  have hd := digitSum_mul a b
  rw [h] at hd
  exact hd.symm

/-- **Soundness of the addition check.** If `a + b = c` then
`S(a) + S(b) ≡ S(c) (mod 9)`. -/
theorem check_add (a b c : ℕ) (h : a + b = c) : S a + S b ≡ S c [MOD 9] := by
  have hd := digitSum_add a b
  rw [h] at hd
  exact hd.symm

/-! ## Part IV: The alternating rule for 11

Divisibility by 11 is governed not by the digit sum but by the *alternating*
digit sum, because `10 ≡ -1 (mod 11)`. Mathlib phrases this over `ℤ`. -/

/-- The alternating decimal digit sum of `n`, as an integer. -/
def altS (n : ℕ) : ℤ := ((Nat.digits 10 n).map (fun d : ℕ => (d : ℤ))).alternatingSum

/-- `n ≡ altS(n) (mod 11)`: the alternating-sum congruence. -/
theorem modEq_eleven (n : ℕ) : (n : ℤ) ≡ altS n [ZMOD 11] :=
  Nat.modEq_eleven_digits_sum n

/-- **Divisibility rule for 11.** `n` is divisible by 11 iff its alternating
digit sum is. -/
theorem eleven_dvd_iff (n : ℕ) : (11 : ℤ) ∣ (n : ℤ) ↔ (11 : ℤ) ∣ altS n := by
  rw [← Int.modEq_zero_iff_dvd, ← Int.modEq_zero_iff_dvd]
  exact ⟨(modEq_eleven n).symm.trans, (modEq_eleven n).trans⟩

/-! ## Part V: Worked instances

These require no digit computation — they follow abstractly from the
compatibility laws, illustrating the check on genuine arithmetic identities. -/

/-- Casting out nines on `12 · 12 = 144`: `S(12)·S(12) ≡ S(144) (mod 9)`. -/
example : S 12 * S 12 ≡ S 144 [MOD 9] := check_mul 12 12 144 (by norm_num)

/-- Casting out nines on `123 · 456 = 56088`. -/
example : S 123 * S 456 ≡ S 56088 [MOD 9] := check_mul 123 456 56088 (by norm_num)

/-- The additive check on `999 + 1 = 1000`. -/
example : S 999 + S 1 ≡ S 1000 [MOD 9] := check_add 999 1 1000 (by norm_num)

end CastingOutNines
