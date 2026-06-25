/-
Quadratic Reciprocity — the Jacobi symbol generalization, and the limit of its
residue-detection (research leaf: quadratic-reciprocity-oq-04)

Source problem family: https://erdosproblems.com (quadratic reciprocity)
Status: original supporting theory; fully machine-checked.

Context:
The Jacobi symbol J(a | b) extends the Legendre symbol to odd b > 0 by
multiplicativity over the prime factorization of b, and it satisfies the same
quadratic reciprocity law (Mathlib: `jacobiSym.quadratic_reciprocity`), which is
what makes the symbol efficiently computable WITHOUT factoring b.

A subtle and important point — the one that powers the Solovay–Strassen
primality test and the notion of "Euler liar" — is that this generalization
LOSES the residue-detection property of the Legendre symbol:

  * For a PRIME p, J(a | p) is the Legendre symbol, so J(a | p) = 1 ⇔ a is a
    nonzero square mod p (Mathlib: `ZMod.isSquare_of_jacobiSym_eq_one`,
    `ZMod.nonsquare_iff_jacobiSym_eq_neg_one`).
  * For COMPOSITE b this equivalence FAILS in the `= 1` direction:
    J(a | b) = 1 does NOT imply that a is a square mod b.

What survives for all b is only the one-way test `J(a | b) = -1 ⟹ a is a
non-square mod b` (Mathlib: `ZMod.nonsquare_of_jacobiSym_eq_neg_one`).

This file makes the failure of the converse explicit and machine-checked with
the smallest classical witness: a = 2, b = 15.

  * `jacobiSym_two_fifteen` — J(2 | 15) = 1.
  * `jacobiSym_two_fifteen_factor` — J(2 | 15) = J(2 | 3)·J(2 | 5), the
        multiplicative decomposition that defines the Jacobi generalization.
  * `two_nonsquare_mod_fifteen` — 2 is not a square in ℤ/15.
  * `jacobi_one_not_isSquare_of_composite` — there is an odd composite b and an
        a with J(a | b) = 1 yet a not a square mod b (so the prime-only
        `isSquare_of_jacobiSym_eq_one` cannot be relaxed to composite b).
  * `jacobiSym_neg_one_imp_nonsquare` — the surviving one-way direction, valid
        for every b (re-exported from Mathlib to frame the contrast).

Reference: Solovay–Strassen primality test; the J(a|n)=1 non-squares are the
"Euler liars".

Tags: quadratic-reciprocity, jacobi-symbol, legendre-symbol, quadratic-residue, number-theory
-/

import Mathlib

namespace QuadraticReciprocityJacobi

/-- The Jacobi symbol `J(2 | 15)` equals `1`. -/
theorem jacobiSym_two_fifteen : jacobiSym 2 15 = 1 := by norm_num

/-- The defining multiplicative decomposition of the Jacobi symbol over the
factorization `15 = 3 · 5`. Each factor is the Legendre symbol `(2 | p) = -1`,
and the two `-1`s multiply to `+1` — this is exactly how a non-square can hide
behind a Jacobi value of `1`. -/
theorem jacobiSym_two_fifteen_factor :
    jacobiSym 2 15 = jacobiSym 2 3 * jacobiSym 2 5 := by
  have h : (15 : ℕ) = 3 * 5 := by norm_num
  rw [h, jacobiSym.mul_right]

/-- `2` is not a square in `ℤ/15` (the squares mod 15 are `{0,1,4,6,9,10}`). -/
theorem two_nonsquare_mod_fifteen : ¬ IsSquare (2 : ZMod 15) := by decide

/-- **The converse of `isSquare_of_jacobiSym_eq_one` fails for composite moduli.**
There is an odd composite `b` and an `a` with `J(a | b) = 1` yet `a` is not a
square modulo `b`. Hence Mathlib's prime-only implication
`J(a | p) = 1 → IsSquare (a : ZMod p)` genuinely requires `p` to be prime: the
witness `a = 2`, `b = 15` is an "Euler liar". -/
theorem jacobi_one_not_isSquare_of_composite :
    ∃ (a : ℤ) (b : ℕ), ¬ b.Prime ∧ Odd b ∧ jacobiSym a b = 1 ∧
      ¬ IsSquare (a : ZMod b) := by
  refine ⟨2, 15, by decide, by decide, jacobiSym_two_fifteen, ?_⟩
  have hcast : ((2 : ℤ) : ZMod 15) = (2 : ZMod 15) := by push_cast; ring
  rw [hcast]
  exact two_nonsquare_mod_fifteen

/-- **The direction that survives for all `b`** (re-exported from Mathlib for
contrast): a Jacobi value of `-1` always certifies a non-square, even for
composite `b`. Together with the previous theorem this pins down exactly what
the Jacobi symbol can and cannot detect. -/
theorem jacobiSym_neg_one_imp_nonsquare {a : ℤ} {b : ℕ} (h : jacobiSym a b = -1) :
    ¬ IsSquare (a : ZMod b) :=
  ZMod.nonsquare_of_jacobiSym_eq_neg_one h

end QuadraticReciprocityJacobi
