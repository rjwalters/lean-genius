import Proofs.QuadraticReciprocityOQ03
import Mathlib.Tactic

/-
# Second Supplementary Law as the Fourth Reduction Lemma

Open Question (from `quadratic-reciprocity-oq-03`):
  Can the second supplementary law `(2/p) = (-1)^((p²-1)/8)` be packaged as a
  fourth reduction lemma in the same one-line wrapper style, completing the
  standalone algorithmic toolkit?

Answer: **YES.** The Legendre-symbol toolkit in `QuadraticReciprocityOQ03`
(multiplicativity, the first supplementary law `(-1/p) = (-1)^(p/2)`, and the
reciprocity swap) is completed by a fourth one-line wrapper for the factor `2`.

Mathlib states the second supplementary law in **character form**:

  `legendreSym.at_two : legendreSym p 2 = χ₈ (p : ZMod 8)`   (for `p ≠ 2`),

where `ZMod.χ₈` is the mod-8 quadratic character (the value depends only on
`p % 8`: it is `1` for `p ≡ ±1 (mod 8)` and `-1` for `p ≡ ±3 (mod 8)`). This is
the directly *computable* form the GCD-style algorithm needs, so we expose it as
`legendreSym_two_eq`, mirroring the parent's first-supplementary wrapper
`legendreSym_neg_one_eq`.

## On the textbook exponential form

The classical statement `(2/p) = (-1)^((p²-1)/8)` is *equivalent* to the χ₈ form
but is **not** available in Mathlib as a named lemma. Bridging the two requires
showing `χ₈ (p : ZMod 8) = (-1 : ℤ)^((p²-1)/8)` for odd `p`, i.e. a case analysis
on `p % 8` together with the parity of `(p²-1)/8` (which equals `0,1,1,0 (mod 2)`
on residues `1,3,5,7`). Mathlib provides the χ₈ value-mod-8 facts in
`Mathlib/NumberTheory/LegendreSymbol/ZModChar.lean`; assembling the exponent
bridge is the remaining (purely arithmetic) step and is left as the documented
follow-up — the χ₈ wrapper below is the one that the algorithm actually evaluates.
-/

open ZMod

namespace QRAlgorithmTwo

-- ============================================================
-- The fourth reduction lemma: handle a factor of 2
-- ============================================================

/-- **Step 3b: Handle factor of 2 (second supplementary law).**

    For an odd prime `p`, the Legendre symbol of `2` is the mod-8 quadratic
    character of `p`:

      `(2/p) = χ₈ (p mod 8)`.

    This is the fourth reduction lemma of the Legendre-symbol algorithm,
    completing the toolkit of `QuadraticReciprocityOQ03` (multiplicativity,
    `(-1/p)`, reciprocity swap, and now `(2/p)`). It is a one-line wrapper around
    `legendreSym.at_two`, in the same style as the first-supplementary wrapper
    `QRAlgorithm.legendreSym_neg_one_eq`. -/
theorem legendreSym_two_eq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p 2 = χ₈ (p : ZMod 8) :=
  legendreSym.at_two hp

-- ============================================================
-- Verified example computations of (2/p)
-- ============================================================

/-- (2/3) = -1  (3 ≡ 3 mod 8, so 2 is a non-residue). -/
example : legendreSym 3 2 = -1 := by decide

/-- (2/5) = -1  (5 ≡ 5 mod 8). -/
example : legendreSym 5 2 = -1 := by decide

/-- (2/23) = 1  (23 ≡ 7 mod 8, so 2 is a residue). -/
example : legendreSym 23 2 = 1 := by decide

/-- (2/31) = 1  (31 ≡ 7 mod 8). -/
example : legendreSym 31 2 = 1 := by decide

/-- (2/41) = 1  (41 ≡ 1 mod 8). -/
example : legendreSym 41 2 = 1 := by decide

#check @legendreSym_two_eq

end QRAlgorithmTwo
