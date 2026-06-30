/-
  Euler's Criterion for quadratic residues, and the Legendre symbol as a power.

  Let `p` be an ODD prime and `a ≢ 0 (mod p)`.  **Euler's criterion** states

      a is a quadratic residue mod p   ⟺   a^((p−1)/2) ≡ 1 (mod p),

  and dually, since `a^((p−1)/2)` squares to `a^(p−1) = 1` (Fermat) it is
  always `±1`, so

      a is a NON-residue                ⟺   a^((p−1)/2) ≡ −1 (mod p).

  The **Legendre symbol** `(a | p)` packages this: as an element of `ZMod p`,

      (a | p) ≡ a^((p−1)/2),

  and it is completely multiplicative, `(ab | p) = (a | p)(b | p)`.

  Mathlib supplies `ZMod.euler_criterion` (in the form `a^(p/2) = 1`, with
  `p/2 = (p−1)/2` for odd `p`) and the Legendre-symbol API; this file states
  the textbook `(p−1)/2` forms, derives the ±1 dichotomy and the non-residue
  characterisation, and verifies everything numerically modulo 7.  Fully
  verified: 0 sorries, 0 axioms, no `native_decide` (the concrete checks use
  `decide`).
-/
import Mathlib

open ZMod

namespace EulerCriterionSquaresOQ01

variable (p : ℕ) [Fact p.Prime] [Fact (2 < p)]

/-- For an odd prime, `p / 2 = (p − 1) / 2` — the exponent in Euler's criterion. -/
theorem half_eq : p / 2 = (p - 1) / 2 := by
  have hp : p % 2 = 1 :=
    (Fact.out : p.Prime).eq_two_or_odd.resolve_left (by have := (Fact.out : 2 < p); omega)
  omega

/-- **Euler's criterion.** For an odd prime `p` and `a ≠ 0` in `ZMod p`,
`a` is a square iff `a^((p−1)/2) = 1`. -/
theorem isSquare_iff_pow {a : ZMod p} (ha : a ≠ 0) :
    IsSquare a ↔ a ^ ((p - 1) / 2) = 1 := by
  rw [← half_eq p]; exact euler_criterion p ha

/-- The criterion value `a^((p−1)/2)` is always `±1` for `a ≠ 0`: it squares to
`a^(p−1) = 1` by Fermat's little theorem, and `ZMod p` is a field. -/
theorem pow_half_eq_one_or_neg_one {a : ZMod p} (ha : a ≠ 0) :
    a ^ ((p - 1) / 2) = 1 ∨ a ^ ((p - 1) / 2) = -1 := by
  have hp : p % 2 = 1 :=
    (Fact.out : p.Prime).eq_two_or_odd.resolve_left (by have := (Fact.out : 2 < p); omega)
  rw [← mul_self_eq_one_iff, ← pow_add, show (p - 1) / 2 + (p - 1) / 2 = p - 1 from by omega]
  exact pow_card_sub_one_eq_one ha

/-- `(1 : ZMod p) ≠ -1` for an odd prime: otherwise `2 = 0`, forcing `p ∣ 2`. -/
theorem one_ne_neg_one : (1 : ZMod p) ≠ -1 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; linear_combination h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  have : 2 < p := Fact.out
  omega

/-- **Non-residues.** For an odd prime `p` and `a ≠ 0`, `a` is a NON-square iff
`a^((p−1)/2) = −1`. -/
theorem not_isSquare_iff_pow {a : ZMod p} (ha : a ≠ 0) :
    ¬ IsSquare a ↔ a ^ ((p - 1) / 2) = -1 := by
  rw [isSquare_iff_pow p ha]
  constructor
  · intro h
    rcases pow_half_eq_one_or_neg_one p ha with h1 | h1
    · exact absurd h1 h
    · exact h1
  · intro h h1
    rw [h1] at h
    exact one_ne_neg_one p h

/-- **Legendre symbol as a power.** As an element of `ZMod p`,
`(a | p) ≡ a^((p−1)/2)`. -/
theorem legendreSym_eq_pow (a : ℤ) :
    (legendreSym p a : ZMod p) = (a : ZMod p) ^ ((p - 1) / 2) := by
  rw [← half_eq p]; exact legendreSym.eq_pow p a

omit [Fact (2 < p)] in
/-- **Multiplicativity of the Legendre symbol**: `(ab | p) = (a | p)(b | p)`. -/
theorem legendreSym_mul (a b : ℤ) :
    legendreSym p (a * b) = legendreSym p a * legendreSym p b :=
  legendreSym.mul p a b

/-! ### Concrete checks modulo 7 (decide, no native_decide) -/

/-- `2` is a quadratic residue mod 7, witnessed by `3² = 2`. -/
theorem isSquare_two_mod_seven : IsSquare (2 : ZMod 7) := ⟨3, by decide⟩

/-- `3` is a quadratic non-residue mod 7. -/
theorem not_isSquare_three_mod_seven : ¬ IsSquare (3 : ZMod 7) := by decide

/-- Euler's criterion in action: `2^((7−1)/2) = 2³ = 1` in `ZMod 7`
(confirming `2` is a residue). -/
theorem two_pow_three_mod_seven : (2 : ZMod 7) ^ 3 = 1 := by decide

/-- And `3^((7−1)/2) = 3³ = −1` in `ZMod 7` (confirming `3` is a non-residue). -/
theorem three_pow_three_mod_seven : (3 : ZMod 7) ^ 3 = -1 := by decide

end EulerCriterionSquaresOQ01
