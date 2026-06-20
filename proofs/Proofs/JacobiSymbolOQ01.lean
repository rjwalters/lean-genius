/-
  The Jacobi symbol: a bimultiplicative, one-sided residue test.

  The **Jacobi symbol** `J(a | n)` extends the Legendre symbol to all odd
  moduli `n` by multiplying the Legendre symbols over the prime factors of `n`:
  `J(a | n) = ∏_{p ∣ n} (a | p)` (with multiplicity).  Its key properties:

    * **bimultiplicativity** in both arguments,
        `J(ab | n) = J(a | n) J(b | n)`,  `J(a | mn) = J(a | m) J(a | n)`;
    * the **trichotomy** `J(a | n) ∈ {−1, 0, 1}`, with `J(a | n) = 0` exactly
      when `gcd(a, n) ≠ 1`;
    * a **one-sided obstruction**: `J(a | n) = −1 ⟹ a is a non-residue mod n`.

  Crucially the obstruction is ONE-SIDED: unlike the Legendre symbol, the
  converse FAILS for composite `n`.  We exhibit `J(2 | 15) = 1` even though `2`
  is a quadratic non-residue mod 15 — so `J(a | n) = 1` does NOT certify that
  `a` is a square.  (This one-sidedness is exactly why the Jacobi symbol speeds
  up the Legendre-symbol computation in reciprocity without itself detecting
  residues.)

  Vehicles are Mathlib's `jacobiSym` API; the concrete `J(2 | 15) = 1` and the
  non-residue are checked by `decide`.  Fully verified: 0 sorries, 0 axioms, no
  `native_decide`.
-/
import Mathlib

namespace JacobiSymbolOQ01

/-! ### Bimultiplicativity and the trichotomy -/

/-- **Multiplicativity in the numerator**: `J(a₁a₂ | n) = J(a₁ | n) J(a₂ | n)`. -/
theorem jacobi_mul_left (a₁ a₂ : ℤ) (n : ℕ) :
    jacobiSym (a₁ * a₂) n = jacobiSym a₁ n * jacobiSym a₂ n :=
  jacobiSym.mul_left a₁ a₂ n

/-- **Multiplicativity in the modulus**: `J(a | m·n) = J(a | m) J(a | n)`. -/
theorem jacobi_mul_right (a : ℤ) (m n : ℕ) [NeZero m] [NeZero n] :
    jacobiSym a (m * n) = jacobiSym a m * jacobiSym a n :=
  jacobiSym.mul_right a m n

/-- **Trichotomy** for coprime arguments: `J(a | n) = ±1`. -/
theorem jacobi_eq_one_or_neg_one {a : ℤ} {n : ℕ} (h : a.gcd n = 1) :
    jacobiSym a n = 1 ∨ jacobiSym a n = -1 :=
  jacobiSym.eq_one_or_neg_one h

/-- `J(a | n) = 0` exactly when `a` and `n` are NOT coprime. -/
theorem jacobi_eq_zero_iff {a : ℤ} {n : ℕ} [NeZero n] :
    jacobiSym a n = 0 ↔ a.gcd n ≠ 1 :=
  jacobiSym.eq_zero_iff_not_coprime

/-! ### The one-sided obstruction, and the failure of its converse -/

/-- **Non-residue obstruction**: if `J(a | n) = −1` then `a` is a quadratic
non-residue modulo `n`. -/
theorem not_isSquare_of_jacobi_eq_neg_one {a : ℤ} {n : ℕ} (h : jacobiSym a n = -1) :
    ¬ IsSquare (a : ZMod n) :=
  ZMod.nonsquare_of_jacobiSym_eq_neg_one h

/-- `J(2 | 15) = 1` — the Jacobi symbol is `(2 | 3)(2 | 5) = (−1)(−1) = 1`. -/
theorem jacobi_two_fifteen : jacobiSym 2 15 = 1 := by norm_num

/-- Yet `2` is a quadratic NON-residue mod 15 (the squares mod 15 are
`{0, 1, 4, 6, 9, 10}`). -/
theorem not_isSquare_two_mod_fifteen : ¬ IsSquare (2 : ZMod 15) := by decide

/-- **The converse fails for composite moduli.** There exist `a, n` with
`J(a | n) = 1` yet `a` a non-residue mod `n`: the Jacobi symbol is a one-sided
witness, not a residue test (unlike the Legendre symbol). -/
theorem jacobi_one_not_isSquare :
    ∃ (a : ℤ) (n : ℕ), jacobiSym a n = 1 ∧ ¬ IsSquare (a : ZMod n) :=
  ⟨2, 15, jacobi_two_fifteen, not_isSquare_two_mod_fifteen⟩

end JacobiSymbolOQ01
