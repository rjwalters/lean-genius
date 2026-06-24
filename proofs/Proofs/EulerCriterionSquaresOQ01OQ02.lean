/-
# Euler's Criterion OQ-01-OQ-02: the two supplementary laws of quadratic reciprocity

The parent `euler-criterion-squares-oq-01` (`EulerCriterionSquaresOQ01.lean`) proved **Euler's
criterion** in Legendre-symbol form,

  `(a | p) ≡ a^((p−1)/2)  (mod p)`   (`legendreSym_eq_pow`),

together with the fact that `a^((p−1)/2)` is always `±1` for `a ≠ 0`.

This leaf derives the **two supplementary laws of quadratic reciprocity**:

1. **First supplementary law** — the value of `(−1 | p)`:
   `(−1 | p) = (−1)^((p−1)/2)`, and `−1` is a square mod `p` iff `p ≡ 1 (mod 4)`.
   This is obtained *directly from the parent's Euler criterion*: the integer `(−1 | p)` and
   the integer `(−1)^((p−1)/2)` are both `±1` and are congruent mod `p`, hence equal (two
   distinct elements of `{−1, 1}` cannot coincide modulo an odd prime).

2. **Second supplementary law** — the value of `(2 | p)` is governed by `p (mod 8)`:
   `2` is a square mod `p` iff `p ≡ ±1 (mod 8)`, equivalently `(2 | p) = 1 ⟺ p ≡ 1, 7 (mod 8)`
   and `(2 | p) = −1 ⟺ p ≡ 3, 5 (mod 8)`. The hard arithmetic content here (the Gauss-sum
   evaluation `(2 | p) = χ₈ p`) is supplied by Mathlib's `ZMod.exists_sq_eq_two_iff`; this file
   packages it into the explicit residue dictionary and reconciles it with the criterion.

## What this proves

* `legendreSym_neg_one`   — `(−1 | p) = (−1)^((p−1)/2)`   (derived from Euler's criterion).
* `neg_one_isSquare_iff`  — `IsSquare (−1) ↔ p % 4 = 1`.
* `legendreSym_neg_one_eq_one_iff` — `(−1 | p) = 1 ↔ p % 4 = 1`.
* `two_isSquare_iff`      — `IsSquare (2) ↔ p % 8 = 1 ∨ p % 8 = 7`.
* `legendreSym_two_eq_one_iff`     — `(2 | p) = 1 ↔ p % 8 = 1 ∨ p % 8 = 7`.
* `legendreSym_two_eq_neg_one_iff` — `(2 | p) = −1 ↔ p % 8 = 3 ∨ p % 8 = 5`.

All results are machine-checked: `0` `sorry`, `0` `axiom`, no `native_decide`.
-/
import Mathlib
import Proofs.EulerCriterionSquaresOQ01

open ZMod

namespace EulerCriterionSquaresOQ01OQ02

variable (p : ℕ) [Fact p.Prime] [Fact (2 < p)]

/-- `p` is odd: `p % 2 = 1`. -/
private theorem p_odd : p % 2 = 1 :=
  (Fact.out : p.Prime).eq_two_or_odd.resolve_left (by have := (Fact.out : 2 < p); omega)

omit [Fact p.Prime] in
/-- `p ≠ 2`, the hypothesis required by Mathlib's supplementary-law lemmas. -/
private theorem p_ne_two : p ≠ 2 := by have := (Fact.out : 2 < p); omega

/-- **Casting `{−1, 1}` is injective modulo an odd prime.** Two integers, each equal to `1`
or `−1`, that have the same image in `ZMod p` are equal. This is the bridge that lets us lift
the Euler-criterion *congruence* to an *equality* of Legendre-symbol values. -/
theorem intCast_inj_of_pm_one {x y : ℤ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1)
    (h : (x : ZMod p) = (y : ZMod p)) : x = y := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rfl
  · exact absurd (by push_cast at h; exact h) (EulerCriterionSquaresOQ01.one_ne_neg_one p)
  · exact absurd (by push_cast at h; exact h.symm) (EulerCriterionSquaresOQ01.one_ne_neg_one p)
  · rfl

/-- `(−1)^n` is always `1` or `−1` in `ℤ`. -/
private theorem neg_one_pow_pm (n : ℕ) : (-1 : ℤ) ^ n = 1 ∨ (-1 : ℤ) ^ n = -1 := by
  rcases Nat.even_or_odd n with he | ho
  · exact Or.inl he.neg_one_pow
  · exact Or.inr ho.neg_one_pow

/-- **First supplementary law (value form).** `(−1 | p) = (−1)^((p−1)/2)`.

Proved straight from the parent's Euler criterion: both sides lie in `{−1, 1}` and are
congruent mod `p` (the criterion `legendreSym_eq_pow`), so they are equal by
`intCast_inj_of_pm_one`. -/
theorem legendreSym_neg_one :
    legendreSym p (-1) = (-1 : ℤ) ^ ((p - 1) / 2) := by
  refine intCast_inj_of_pm_one p ?_ (neg_one_pow_pm ((p - 1) / 2)) ?_
  · -- `(−1 | p) ∈ {1, −1}` since `(−1 : ZMod p) ≠ 0`
    refine legendreSym.eq_one_or_neg_one p ?_
    push_cast; exact neg_ne_zero.mpr one_ne_zero
  · -- the congruence `(−1 | p) ≡ (−1)^((p−1)/2) (mod p)` is exactly Euler's criterion
    rw [EulerCriterionSquaresOQ01.legendreSym_eq_pow]
    push_cast
    ring

/-- **First supplementary law (residue form).** `−1` is a quadratic residue mod `p` iff
`p ≡ 1 (mod 4)`. -/
theorem neg_one_isSquare_iff : IsSquare (-1 : ZMod p) ↔ p % 4 = 1 := by
  rw [ZMod.exists_sq_eq_neg_one_iff]
  have := p_odd p
  omega

/-- `(−1 | p) = 1` iff `p ≡ 1 (mod 4)`. -/
theorem legendreSym_neg_one_eq_one_iff : legendreSym p (-1) = 1 ↔ p % 4 = 1 := by
  rw [legendreSym.eq_one_iff p (by push_cast; exact neg_ne_zero.mpr one_ne_zero)]
  rw [show ((-1 : ℤ) : ZMod p) = (-1 : ZMod p) by push_cast; ring]
  exact neg_one_isSquare_iff p

/-- `((2 : ℤ) : ZMod p) ≠ 0`, since `p > 2` is prime and so does not divide `2`. -/
private theorem two_ne_zero' : ((2 : ℤ) : ZMod p) ≠ 0 := by
  have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    have := (Fact.out : 2 < p)
    omega
  exact_mod_cast h2

/-- **Second supplementary law (residue form).** `2` is a quadratic residue mod `p` iff
`p ≡ ±1 (mod 8)`. The deep content (the Gauss-sum value `(2 | p) = χ₈ p`) is Mathlib's
`ZMod.exists_sq_eq_two_iff`. -/
theorem two_isSquare_iff : IsSquare (2 : ZMod p) ↔ p % 8 = 1 ∨ p % 8 = 7 :=
  ZMod.exists_sq_eq_two_iff (p_ne_two p)

/-- `(2 | p) = 1` iff `p ≡ 1 or 7 (mod 8)`. -/
theorem legendreSym_two_eq_one_iff :
    legendreSym p 2 = 1 ↔ p % 8 = 1 ∨ p % 8 = 7 := by
  rw [legendreSym.eq_one_iff p (two_ne_zero' p)]
  rw [show ((2 : ℤ) : ZMod p) = (2 : ZMod p) by push_cast; ring]
  exact two_isSquare_iff p

/-- `(2 | p) = −1` iff `p ≡ 3 or 5 (mod 8)`. -/
theorem legendreSym_two_eq_neg_one_iff :
    legendreSym p 2 = -1 ↔ p % 8 = 3 ∨ p % 8 = 5 := by
  rw [legendreSym.eq_neg_one_iff p]
  rw [show ((2 : ℤ) : ZMod p) = (2 : ZMod p) by push_cast; ring]
  rw [two_isSquare_iff p]
  have := p_odd p
  omega

end EulerCriterionSquaresOQ01OQ02
