/-
  The Combined ("Third") Supplement to Quadratic Reciprocity, the Zolotarev Way
  (elementary-quadratic-reciprocity-oq-01-oq-03-oq-01-oq-01-oq-01-oq-01-oq-01-oq-02-oq-02)

  Open Question (follow-up of the second-supplement entry
  oq-01-oq-03-oq-01-oq-01-oq-01-oq-01-oq-01-oq-02): having the first supplement
  `a = -1` and the second supplement `a = 2` as Zolotarev permutation signs,
  FUSE them into the combined supplement for `a = -2` — its explicit power form,
  its mod-8 characterization, and its reading as the sign of the Zolotarev
  permutation `x ↦ -2·x` on ℤ/n.

  This file delivers the combined supplement, `a = -2`:

      J(-2 | n) = (-1) ^ ((n - 1) / 2 + (n² - 1) / 8)      for every odd n > 0,

  and identifies it as the sign of the permutation `x ↦ -2·x` on ℤ/n (the
  Zolotarev permutation of the unit `-2`).

  ## The route

  Multiplicativity of the Jacobi symbol in its top argument
  (`jacobiSym.mul_left`) splits `-2 = (-1)·2`, so

      J(-2 | n) = J(-1 | n) · J(2 | n).

  The two factors are exactly the first and second supplements, already proved
  in the sibling entries as Zolotarev permutation signs:

      J(-1 | n) = (-1) ^ ((n - 1) / 2)          (sign of `x ↦ -x`),
      J( 2 | n) = (-1) ^ ((n² - 1) / 8)         (sign of `x ↦ 2·x`).

  Combining via `(-1)^a · (-1)^b = (-1)^(a+b)` gives the fused exponent
  `(n - 1) / 2 + (n² - 1) / 8`.  A residue computation mod 8 then yields the
  classical characterization

      -2 is a quadratic residue mod p   ⟺   p ≡ 1 or 3  (mod 8).

  ## Honest comparison with Mathlib

  Mathlib already supplies the *value* `jacobiSym.at_neg_two : J(-2 | n) = χ₈' n`
  and the case split `χ₈'_nat_eq_if_mod_eight`.  The genuinely NEW content here
  is, exactly as for the second supplement:
  * the explicit `(-1)^((n-1)/2 + (n²-1)/8)` POWER form of `χ₈'` (the `-2`
    analogue of the parent's `chi8_eq_neg_one_pow`), which Mathlib does not give; and
  * its reading as the sign of Zolotarev's permutation `x ↦ -2·x`, fusing the two
    elementary supplement permutations into one — squarely in the spirit of
    Zolotarev (1872) / Frobenius (1914).

  Content (all 0 sorries, 0 axioms):
  * `jacobiSym_neg_two`        — power form `J(-2|n) = (-1)^((n-1)/2 + (n²-1)/8)`.
  * `jacobiSym_neg_two_eq`     — mod-8 indicator `= +1 iff n ≡ 1,3 (mod 8)`.
  * `chi8'_eq_neg_one_pow`     — the NEW power formula `χ₈' n = (-1)^((n-1)/2+(n²-1)/8)`.
  * `neg_one_pow_neg_two`      — the fused exponent's value as a mod-8 indicator.
  * `sign_ringMulPerm_neg_two` — the `x ↦ -2·x` permutation sign (unit form).
  * `sign_neg_two`             — the canonical (hypothesis-free) `x ↦ -2·x` statement.
  * `legendreSym_neg_two`      — Euler's criterion at an odd prime, power form.
  * `legendreSym_neg_two_eq`   — the prime mod-8 indicator.
  * `neg_two_qr_iff`           — "-2 is a QR mod p ⟺ p ≡ 1,3 (mod 8)".

  References:
  - Zolotarev (1872): Nouvelle démonstration de la loi de réciprocité de Legendre
  - Frobenius (1914): generalization to Jacobi symbols / composite moduli
-/
import Proofs.ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01OQ02
import Proofs.ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01OQ01

set_option maxHeartbeats 800000

namespace ZolotarevThirdSupplement

open Equiv Equiv.Perm
open ZolotarevCRT (ringMulPerm)
open ZolotarevFirstSupplement (jacobiSym_neg_one)
open ZolotarevSecondSupplement (jacobiSym_two)

variable {n : ℕ} [NeZero n]

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: THE POWER FORM OF THE COMBINED SUPPLEMENT  J(-2 | n)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Combined supplementary law of quadratic reciprocity, via Zolotarev.**
    For every odd `n > 0`,

        J(-2 | n) = (-1) ^ ((n - 1) / 2 + (n² - 1) / 8).

    Proof: `jacobiSym.mul_left` splits `-2 = (-1)·2`; the two factors are the
    first and second supplements `J(-1|n) = (-1)^((n-1)/2)` and
    `J(2|n) = (-1)^((n²-1)/8)`; `pow_add` fuses the exponents. -/
theorem jacobiSym_neg_two (hodd : Odd n) :
    jacobiSym (-2) n = (-1 : ℤ) ^ ((n - 1) / 2 + (n ^ 2 - 1) / 8) := by
  have h : (-2 : ℤ) = -1 * 2 := by ring
  rw [h, jacobiSym.mul_left, jacobiSym_neg_one hodd, jacobiSym_two hodd, ← pow_add]

/-- **Mod-8 indicator for the combined supplement.**  For odd `n`,

        J(-2 | n) = (if n % 8 = 1 ∨ n % 8 = 3 then 1 else -1),

    i.e. `-2` is a quadratic residue exactly for `n ≡ 1, 3 (mod 8)`.  This is the
    value form, read off Mathlib's `χ₈'`. -/
theorem jacobiSym_neg_two_eq (hodd : Odd n) :
    jacobiSym (-2) n = if n % 8 = 1 ∨ n % 8 = 3 then 1 else -1 := by
  rw [jacobiSym.at_neg_two hodd, ZMod.χ₈'_nat_eq_if_mod_eight,
    if_neg (show ¬ (n % 2 = 0) by have := Nat.odd_iff.mp hodd; omega)]

/-- **Closed-form power formula for `χ₈'`.**  For every odd `n`,

        χ₈' n = (-1) ^ ((n - 1) / 2 + (n² - 1) / 8).

    Mathlib supplies only the mod-8 case split `χ₈'_nat_eq_if_mod_eight`; this is
    the explicit power form, the `-2` analogue of the second supplement's
    `chi8_eq_neg_one_pow`. -/
theorem chi8'_eq_neg_one_pow (hodd : Odd n) :
    ZMod.χ₈' (n : ZMod 8) = (-1 : ℤ) ^ ((n - 1) / 2 + (n ^ 2 - 1) / 8) := by
  rw [ZMod.χ₈'_nat_eq_if_mod_eight,
    if_neg (show ¬ (n % 2 = 0) by have := Nat.odd_iff.mp hodd; omega),
    ← jacobiSym_neg_two_eq hodd, jacobiSym_neg_two hodd]

/-- The fused exponent's value as a signed power: `(-1)^((n-1)/2 + (n²-1)/8)` is
    `+1` for `n ≡ 1, 3 (mod 8)` and `-1` for `n ≡ 5, 7 (mod 8)`. -/
theorem neg_one_pow_neg_two (hodd : Odd n) :
    (-1 : ℤ) ^ ((n - 1) / 2 + (n ^ 2 - 1) / 8)
      = if n % 8 = 1 ∨ n % 8 = 3 then 1 else -1 := by
  rw [← jacobiSym_neg_two hodd, jacobiSym_neg_two_eq hodd]

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE ZOLOTAREV PERMUTATION `x ↦ -2·x`
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The `x ↦ -2·x` permutation sign (unit form).**  For odd `n` and any unit
    `u : (ℤ/n)ˣ` whose underlying residue is `-2`, the sign of the Zolotarev
    permutation `x ↦ u·x` (i.e. `x ↦ -2·x`) on the whole ring `ℤ/n` is

        sign(ringMulPerm u) = (-1) ^ ((n - 1) / 2 + (n² - 1) / 8).

    This reads the combined supplement off Zolotarev's permutation of `-2`,
    via the parent full-odd Frobenius identity `sign(ringMulPerm u) = J(-2 | n)`. -/
theorem sign_ringMulPerm_neg_two (hodd : Odd n) (u : (ZMod n)ˣ) (hu : (u : ZMod n) = -2) :
    (Equiv.Perm.sign (ringMulPerm u) : ℤ) = (-1 : ℤ) ^ ((n - 1) / 2 + (n ^ 2 - 1) / 8) := by
  have hA : ((-2 : ℤ) : ZMod n) = (u : ZMod n) := by rw [hu]; push_cast; ring
  rw [ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd hodd u (-2) hA, jacobiSym_neg_two hodd]

/-- **The `x ↦ -2·x` permutation sign (canonical form).**  For odd `n`, `-2` is a
    unit (since `2` is coprime to `n`); the sign of the canonical permutation
    `x ↦ -2·x` on `ℤ/n` is `(-1)^((n-1)/2 + (n²-1)/8)`.  This is the
    hypothesis-free Zolotarev statement of the combined supplement. -/
theorem sign_neg_two (hodd : Odd n) :
    (Equiv.Perm.sign (ringMulPerm (-(ZMod.unitOfCoprime 2
        ((Nat.prime_two.coprime_iff_not_dvd).mpr
          (Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd)))))) : ℤ)
      = (-1 : ℤ) ^ ((n - 1) / 2 + (n ^ 2 - 1) / 8) :=
  sign_ringMulPerm_neg_two hodd _ (by rw [Units.val_neg, ZMod.coe_unitOfCoprime]; push_cast; ring)

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE LEGENDRE-SYMBOL SPECIALIZATION AT AN ODD PRIME
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Euler's criterion / combined supplement for the Legendre symbol.**  For an
    odd prime `p`,

        (-2 / p) = (-1) ^ ((p - 1) / 2 + (p² - 1) / 8),

    obtained by specializing the Jacobi-symbol supplement to a prime modulus. -/
theorem legendreSym_neg_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-2) = (-1 : ℤ) ^ ((p - 1) / 2 + (p ^ 2 - 1) / 8) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  rw [jacobiSym.legendreSym.to_jacobiSym,
    jacobiSym_neg_two ((Fact.out : p.Prime).odd_of_ne_two hp)]

/-- **Mod-8 indicator at an odd prime.**  `(-2 / p) = +1` for `p ≡ 1, 3 (mod 8)`
    and `-1` for `p ≡ 5, 7 (mod 8)`. -/
theorem legendreSym_neg_two_eq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-2) = if p % 8 = 1 ∨ p % 8 = 3 then 1 else -1 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  rw [jacobiSym.legendreSym.to_jacobiSym,
    jacobiSym_neg_two_eq ((Fact.out : p.Prime).odd_of_ne_two hp)]

/-- **Classical characterization: when is `-2` a quadratic residue?**  For an odd
    prime `p`,

        -2 is a quadratic residue mod p   ⟺   p ≡ 1 or 3  (mod 8).

    (Here `legendreSym p (-2) = 1` exactly captures "-2 is a nonzero square".) -/
theorem neg_two_qr_iff (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-2) = 1 ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  rw [legendreSym_neg_two_eq p hp]
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (by norm_num) h

end ZolotarevThirdSupplement

#check @ZolotarevThirdSupplement.jacobiSym_neg_two
#check @ZolotarevThirdSupplement.chi8'_eq_neg_one_pow
#check @ZolotarevThirdSupplement.sign_neg_two
#check @ZolotarevThirdSupplement.legendreSym_neg_two
#check @ZolotarevThirdSupplement.neg_two_qr_iff

