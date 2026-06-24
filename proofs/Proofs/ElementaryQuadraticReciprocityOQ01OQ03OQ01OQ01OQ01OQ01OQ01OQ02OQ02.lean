/-
  The Combined Supplement (a = -2) to Quadratic Reciprocity, the Zolotarev Way
  (elementary-quadratic-reciprocity-oq-01-oq-03-oq-01-oq-01-oq-01-oq-01-oq-01-oq-02-oq-02)

  Open Question (follow-up of the SECOND supplement entry
  oq-…-oq-02, "Power-form characterization of the octic character"):
  give the explicit `(-1)^e` power form for the *companion* octic character
  χ₈' (the one attached to the extension ℚ(√-2)/ℚ), and read the resulting
  third / combined supplementary law `J(-2 | n)` off Zolotarev's permutation.

  This file delivers the COMBINED supplement, a = -2:

      J(-2 | n) = (-1) ^ ((n-1)/2 + (n² - 1)/8)      for every odd n > 0,

  i.e. the product of the first supplement (a = -1, exponent (n-1)/2) and the
  second supplement (a = 2, exponent (n²-1)/8), and identifies it as the sign of
  the permutation x ↦ -2·x on ℤ/n.

  ## What is genuinely new here

  Mathlib supplies the *value* `jacobiSym.at_neg_two : J(-2 | n) = χ₈' n` and the
  mod-8 case split `χ₈'_nat_eq_if_mod_eight`, but NOT a closed `(-1)^e` power
  form for χ₈'.  The new content is the closed power formula

      χ₈' n = (-1) ^ ((n-1)/2 + (n² - 1)/8)      for odd n,

  the octic-companion analogue of `ZMod.χ₄_eq_neg_one_pow`.  It is obtained
  *structurally*, with no fresh parity computation, from the factorisation
  `χ₈' = χ₄ · χ₈` (`ZMod.χ₈'_eq_χ₄_mul_χ₈`) together with
    * `ZMod.χ₄_eq_neg_one_pow` (the quartic power form, exponent (n-1)/2), and
    * `chi8_eq_neg_one_pow` from the parent second-supplement entry
      (the octic power form, exponent (n²-1)/8).
  Adding the two exponents in the single law `(-1)^a · (-1)^b = (-1)^(a+b)`
  yields the combined exponent — exhibiting the multiplicative structure
  J(-2|·) = J(-1|·) · J(2|·) at the level of the *exponents* of the supplements.

  Content (all 0 sorries, 0 axioms):
  * `chi8'_eq_neg_one_pow`        — NEW power formula `χ₈' n = (-1)^((n-1)/2+(n²-1)/8)`.
  * `neg_one_pow_combined`        — its explicit value: +1 on n ≡ 1,3 (8), else -1.
  * `jacobiSym_neg_two`           — THE COMBINED SUPPLEMENT `J(-2|n) = (-1)^(…)`.
  * `jacobiSym_neg_two_eq_if`     — the mod-8 case-split form of the supplement.
  * `jacobiSym_neg_two_eq_mul`    — structural law `J(-2|n) = J(-1|n)·J(2|n)`.
  * `sign_ringMulPerm_neg_two`    — the `x ↦ -2·x` permutation sign equals it.
  * `legendreSym_neg_two`         — prime case `(-2 / p) = (-1)^((p-1)/2+(p²-1)/8)`.
  * `legendreSym_neg_two_eq_one_iff` — recovers `-2` is a QR mod p ⇔ p ≡ 1,3 (8).

  References:
  - Zolotarev (1872); Frobenius (1914), as for the parent supplements.
-/
import Proofs.ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01OQ02

set_option maxHeartbeats 800000

namespace ZolotarevThirdSupplement

open Equiv Equiv.Perm
open ZolotarevCRT (ringMulPerm)

variable {n : ℕ} [NeZero n]

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: THE POWER FORMULA FOR THE COMPANION OCTIC CHARACTER χ₈'
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Closed-form power formula for the companion octic character `χ₈'`.**
    For every odd `n`,

        χ₈' n = (-1) ^ ((n-1)/2 + (n² - 1)/8).

    Mathlib provides only the mod-8 case split `χ₈'_nat_eq_if_mod_eight`; this is
    the explicit power form, the octic-companion analogue of `χ₄_eq_neg_one_pow`.
    It follows structurally from `χ₈' = χ₄ · χ₈`, the quartic power form
    (exponent `(n-1)/2`), and the parent octic power form (exponent `(n²-1)/8`). -/
theorem chi8'_eq_neg_one_pow (hodd : Odd n) :
    ZMod.χ₈' (n : ZMod 8) = (-1 : ℤ) ^ ((n - 1) / 2 + (n ^ 2 - 1) / 8) := by
  have hodd2 : n % 2 = 1 := Nat.odd_iff.mp hodd
  have h2 : (n - 1) / 2 = n / 2 := by omega
  rw [h2, ZMod.χ₈'_eq_χ₄_mul_χ₈, ZMod.cast_natCast (by norm_num : (4 : ℕ) ∣ 8),
    ZMod.χ₄_eq_neg_one_pow hodd2, ZolotarevSecondSupplement.chi8_eq_neg_one_pow hodd,
    ← pow_add]

/-- The combined supplement value as a sign: `(-1)^((n-1)/2+(n²-1)/8)` is `+1`
    for `n ≡ 1, 3 (mod 8)` and `-1` for `n ≡ 5, 7 (mod 8)` — exactly the values
    of `χ₈'`, the residues for which `-2` is a square. -/
theorem neg_one_pow_combined (hodd : Odd n) :
    (-1 : ℤ) ^ ((n - 1) / 2 + (n ^ 2 - 1) / 8)
      = if n % 8 = 1 ∨ n % 8 = 3 then 1 else -1 := by
  rw [← chi8'_eq_neg_one_pow hodd, ZMod.χ₈'_nat_eq_if_mod_eight,
    if_neg (by simp [Nat.odd_iff.mp hodd])]

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE COMBINED (a = -2) SUPPLEMENT TO QUADRATIC RECIPROCITY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Combined supplementary law of quadratic reciprocity, via Zolotarev.**
    For every odd `n > 0`,

        J(-2 | n) = (-1) ^ ((n-1)/2 + (n² - 1)/8).

    Proof: `jacobiSym.at_neg_two` rewrites `J(-2 | n)` as the companion octic
    character `χ₈' n`, and `chi8'_eq_neg_one_pow` puts that in closed power form. -/
theorem jacobiSym_neg_two (hodd : Odd n) :
    jacobiSym (-2) n = (-1 : ℤ) ^ ((n - 1) / 2 + (n ^ 2 - 1) / 8) := by
  rw [jacobiSym.at_neg_two hodd, chi8'_eq_neg_one_pow hodd]

/-- The combined supplement in mod-8 case-split form:
    `J(-2 | n) = +1` for `n ≡ 1, 3 (mod 8)` and `-1` otherwise. -/
theorem jacobiSym_neg_two_eq_if (hodd : Odd n) :
    jacobiSym (-2) n = if n % 8 = 1 ∨ n % 8 = 3 then 1 else -1 := by
  rw [jacobiSym_neg_two hodd, neg_one_pow_combined hodd]

/-- **Structural decomposition of the combined supplement.**  Since `-2 = (-1)·2`,
    multiplicativity of the Jacobi symbol in its numerator factors the combined
    supplement as the product of the first (`a = -1`) and second (`a = 2`)
    supplements:

        J(-2 | n) = J(-1 | n) · J(2 | n).

    Together with `jacobiSym_neg_two` this exhibits the exponent identity
    `(n-1)/2 + (n²-1)/8` as the sum of the two individual supplement exponents.
    (Multiplicativity needs no hypothesis on `n`.) -/
theorem jacobiSym_neg_two_eq_mul (m : ℕ) :
    jacobiSym (-2) m = jacobiSym (-1) m * jacobiSym 2 m := by
  rw [show (-2 : ℤ) = (-1) * 2 by ring, jacobiSym.mul_left]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE ZOLOTAREV PERMUTATION READING AND THE PRIME (LEGENDRE) CASE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The `x ↦ -2·x` permutation sign.**  For odd `n` and any unit
    `u : (ℤ/n)ˣ` whose underlying residue is `-2`, the sign of the Zolotarev
    permutation `x ↦ u·x` (i.e. `x ↦ -2·x`) on the whole ring `ℤ/n` is

        sign(ringMulPerm u) = (-1) ^ ((n-1)/2 + (n² - 1)/8).

    This reads the combined supplement off Zolotarev's permutation, through the
    parent full-odd Frobenius identity `sign(ringMulPerm u) = J(A | n)`. -/
theorem sign_ringMulPerm_neg_two (hodd : Odd n) (u : (ZMod n)ˣ) (hu : (u : ZMod n) = -2) :
    (Equiv.Perm.sign (ringMulPerm u) : ℤ) = (-1 : ℤ) ^ ((n - 1) / 2 + (n ^ 2 - 1) / 8) := by
  have hA : ((-2 : ℤ) : ZMod n) = (u : ZMod n) := by rw [hu]; push_cast; ring
  rw [ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd hodd u (-2) hA, jacobiSym_neg_two hodd]

/-- **Combined supplement for the Legendre symbol.**  For an odd prime `p`,

        (-2 / p) = (-1) ^ ((p-1)/2 + (p² - 1)/8),

    obtained by specializing the Jacobi-symbol supplement to a prime modulus. -/
theorem legendreSym_neg_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-2) = (-1 : ℤ) ^ ((p - 1) / 2 + (p ^ 2 - 1) / 8) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  rw [jacobiSym.legendreSym.to_jacobiSym,
    jacobiSym_neg_two ((Fact.out : p.Prime).odd_of_ne_two hp)]

/-- **The classical `-2` reciprocity criterion, recovered from the power form.**
    For an odd prime `p`, `-2` is a quadratic residue mod `p` iff the combined
    supplement evaluates to `+1`, i.e. iff `p ≡ 1` or `3 (mod 8)`. -/
theorem legendreSym_neg_two_eq_one_iff (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-2) = 1 ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp
  rw [legendreSym_neg_two p hp, neg_one_pow_combined hodd]
  split_ifs with h
  · simp [h]
  · simp [h]

end ZolotarevThirdSupplement

#check @ZolotarevThirdSupplement.chi8'_eq_neg_one_pow
#check @ZolotarevThirdSupplement.jacobiSym_neg_two
#check @ZolotarevThirdSupplement.jacobiSym_neg_two_eq_mul
#check @ZolotarevThirdSupplement.sign_ringMulPerm_neg_two
#check @ZolotarevThirdSupplement.legendreSym_neg_two
#check @ZolotarevThirdSupplement.legendreSym_neg_two_eq_one_iff
