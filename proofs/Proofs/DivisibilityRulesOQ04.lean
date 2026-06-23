import Mathlib.Data.Nat.Digits.Div
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

/-
# Three Divisibility Rules for 11  (divisibility-rules-oq-04)

## Open Question (divisibility-rules-oq-04)
"What are the base-`b` digit rules that detect divisibility by 11, and how do
they all follow from the residues of powers of 10 modulo 11?"

The sibling `divisibility-rules-oq-01` records the classical **alternating
single-digit** rule for 11, but only in *congruence* form
(`11 ∣ n - altDigitSum`) and via `native_decide` (so it is axiom-dependent).
This entry gives three genuinely different, **fully verified (0-axiom)**
biconditionals for `11 ∣ n`, each keyed to a different power of 10 mod 11:

* `10 ≡ -1`   ⇒ alternating sum of single digits  (the schoolbook rule);
* `100 ≡ 1`   ⇒ plain sum of two-digit blocks      (the *new* block-sum rule);
* `1000 ≡ -1` ⇒ alternating sum of three-digit blocks (the rule shared with 7
  and 13, since `1001 = 7·11·13`).

All three are uniform specializations of Mathlib's base-`b` machinery
(`Nat.dvd_iff_dvd_digits_sum` for the `≡ 1` case, `Nat.dvd_iff_dvd_ofDigits`
for the `≡ -1` case), so each is a one-residue computation with no new axioms.
Together with `three_dvd_iff`/`nine_dvd_iff` this completes the mod-3 / mod-9 /
mod-11 divisibility-rule trilogy with a clean alternating-sum case.
-/

namespace DivisibilityRulesOQ04

open Nat

/-- **Two-digit block-sum rule for 11.** Because `100 ≡ 1 (mod 11)`, the base-100
digits (i.e. the two-decimal-digit blocks read from the right) satisfy
`11 ∣ n ↔ 11 ∣ (sum of the blocks)`. This is a new specialization not present in
the sibling entries, which only treat the single-digit alternating rule. -/
theorem eleven_dvd_iff_block_sum (n : ℕ) :
    11 ∣ n ↔ 11 ∣ (Nat.digits 100 n).sum :=
  Nat.dvd_iff_dvd_digits_sum 11 100 (by norm_num) n

/-- **Classical alternating single-digit rule for 11**, as a fully verified
biconditional. Because `10 ≡ -1 (mod 11)`, `11 ∣ n` iff `11` divides the
alternating sum `d₀ - d₁ + d₂ - ⋯` of the decimal digits. The sibling
`divisibility-rules-oq-01` proves only the congruence `11 ∣ n - altSum` and uses
`native_decide`; here the clean iff comes straight from Mathlib with no axioms. -/
theorem eleven_dvd_iff_alternating (n : ℕ) :
    11 ∣ n ↔
      (11 : ℤ) ∣ ((Nat.digits 10 n).map fun d : ℕ => (d : ℤ)).alternatingSum :=
  Nat.eleven_dvd_iff

/-- **Three-digit block alternating rule for 11.** Because `1000 ≡ -1 (mod 11)`
(indeed `1001 = 7·11·13`), `11 ∣ n` iff `11` divides the alternating sum of the
three-decimal-digit blocks of `n`. This is the same grouping that simultaneously
tests divisibility by 7, 11 and 13. -/
theorem eleven_dvd_iff_block_alternating (n : ℕ) :
    11 ∣ n ↔
      (11 : ℤ) ∣ ((Nat.digits 1000 n).map fun d : ℕ => (d : ℤ)).alternatingSum := by
  have h := Nat.dvd_iff_dvd_ofDigits 11 1000 (-1 : ℤ) (by norm_num) n
  rwa [Nat.ofDigits_neg_one] at h

/-- **Underlying congruence.** `n` is congruent to the alternating digit sum
modulo 11 — the residue fact that powers the single-digit rule. -/
theorem eleven_modEq_alternating (n : ℕ) :
    (n : ℤ) ≡ ((Nat.digits 10 n).map fun d : ℕ => (d : ℤ)).alternatingSum [ZMOD 11] :=
  Nat.modEq_eleven_digits_sum n

end DivisibilityRulesOQ04
