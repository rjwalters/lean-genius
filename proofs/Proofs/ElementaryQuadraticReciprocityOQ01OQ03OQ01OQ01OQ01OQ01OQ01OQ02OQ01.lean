/-
  The Third Supplement to Quadratic Reciprocity, the Zolotarev Way
  (elementary-quadratic-reciprocity-oq-01-oq-03-oq-01-oq-01-oq-01-oq-01-oq-01-oq-02-oq-01)

  Open Question (the natural completion of the supplementary-law dictionary built
  by the two sibling supplements oq-…-oq-01 and oq-…-oq-02):
  "Having read `a = -1` and `a = 2` off the Zolotarev permutation sign on ℤ/n,
  combine them into the `a = -2` supplement and extract the classical criterion
  for -2 to be a quadratic residue."

  This file delivers the THIRD supplement, a = -2:

      J(-2 | n) = (-1) ^ ((n-1)/2 + (n²-1)/8)      for every odd n > 0,

  together with the classical residue criterion

      J(-2 | n) = 1   ⇔   n ≡ 1 or 3 (mod 8),

  and identifies J(-2 | n) as the sign of the Zolotarev permutation `x ↦ (-2)·x`
  on the whole ring ℤ/n.

  ## What is genuinely new here, and what is not

  The VALUE J(-2 | n) is classical and even already in Mathlib
  (`jacobiSym.at_neg_two : J(-2 | n) = χ₈' n`, where `χ₈'` is the octic character
  of the field ℚ(√-2)).  As with the two sibling supplements, what this file adds
  beyond Mathlib is:

  * the explicit closed POWER form `χ₈' n = (-1)^((n-1)/2 + (n²-1)/8)` — Mathlib
    only offers the mod-8 case split `χ₈'_nat_eq_if_mod_eight`; this is the octic
    analogue of `ZMod.χ₄_eq_neg_one_pow`, completing the trio with the sibling
    files' `χ₄` and `χ₈` power forms;
  * the reading of the supplement as the sign of Zolotarev's permutation
    `x ↦ (-2)·x`, exactly in the spirit of Zolotarev (1872) / Frobenius (1914);
  * the explicit residue criterion `J(-2 | n) = 1 ⇔ n ≡ 1, 3 (mod 8)` (for an odd
    prime p, the classical statement that `-2` is a quadratic residue mod p iff
    `p ≡ 1, 3 (mod 8)` — equivalently p is represented by the form `x² + 2y²`).

  ## The route

  The third supplement is the product of the first two: by multiplicativity of
  the Jacobi symbol in its numerator (`jacobiSym.mul_left`, since `-2 = (-1)·2`),

      J(-2 | n) = J(-1 | n) · J(2 | n)
                = (-1)^((n-1)/2) · (-1)^((n²-1)/8)        (the two siblings)
                = (-1)^((n-1)/2 + (n²-1)/8).

  The only genuinely new computation is the parity of the combined exponent,
  `exponent_parity`, a clean `m mod 4 ↔ n mod 8` count in the spirit of the
  second supplement's triangular-number parity.  Writing `n = 2m+1`,

      (n-1)/2 + (n²-1)/8 = m + m(m+1)/2,

  whose parity (governed by `m mod 4`, equivalently `n mod 8`) is even exactly
  when `n ≡ 1, 3 (mod 8)`.

  Content (all 0 sorries, 0 axioms):
  * `exponent_parity`             — `((n-1)/2 + (n²-1)/8) % 2 = (n mod 8 ∈ {1,3} ? 0 : 1)`.
  * `neg_one_pow_exponent`        — `(-1)^((n-1)/2 + (n²-1)/8) = (n mod 8 ∈ {1,3} ? 1 : -1)`.
  * `jacobiSym_neg_two`           — THE THIRD SUPPLEMENT (product form).
  * `jacobiSym_neg_two_pow`       — the supplement as a single signed power.
  * `chi8'_eq_neg_one_pow`        — the NEW power formula `χ₈' n = (-1)^(…)`.
  * `jacobiSym_neg_two_eq_chi8'`  — consistency with Mathlib's `jacobiSym.at_neg_two`.
  * `jacobiSym_neg_two_residue`   — the explicit residue form.
  * `jacobiSym_neg_two_eq_one_iff`— THE CRITERION: `J(-2|n) = 1 ⇔ n ≡ 1, 3 (mod 8)`.
  * `sign_ringMulPerm_neg_two`    — the `x ↦ (-2)·x` permutation sign equals the supplement.
  * `legendreSym_neg_two`         — the odd-prime special case `(-2/p) = (-1)^((p-1)/2 + (p²-1)/8)`.
  * `legendreSym_neg_two_eq_one_iff` — `-2` is a QR mod p ⇔ `p ≡ 1, 3 (mod 8)`.

  References:
  - Zolotarev (1872): Nouvelle démonstration de la loi de réciprocité de Legendre
  - Frobenius (1914): generalization to Jacobi symbols / composite moduli
-/
import Proofs.ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01OQ01
import Proofs.ElementaryQuadraticReciprocityOQ01OQ03OQ01OQ01OQ01OQ01OQ01OQ02

set_option maxHeartbeats 800000

namespace ZolotarevThirdSupplement

open Equiv Equiv.Perm
open ZolotarevCRT (ringMulPerm)

variable {n : ℕ} [NeZero n]

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: THE PARITY OF THE COMBINED EXPONENT (n-1)/2 + (n²-1)/8
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Parity of the combined supplement exponent.**  For odd `n`, the exponent
    `(n-1)/2 + (n²-1)/8` is even exactly when `n ≡ 1, 3 (mod 8)`:

        ((n-1)/2 + (n²-1)/8) % 2 = (if n % 8 = 1 ∨ n % 8 = 3 then 0 else 1).

    Writing `n = 2m+1` gives `(n-1)/2 = m` and `(n²-1)/8 = m(m+1)/2`, so the
    exponent is `m + T_m` (a triangular-number-shifted count) whose parity is
    governed by `m mod 4 ↔ n mod 8`; `interval_cases` on `m mod 4` and `omega`
    discharge the whole modular computation. -/
theorem exponent_parity (hodd : Odd n) :
    ((n - 1) / 2 + (n ^ 2 - 1) / 8) % 2 = (if n % 8 = 1 ∨ n % 8 = 3 then 0 else 1) := by
  obtain ⟨m, rfl⟩ := hodd
  have hhalf : (2 * m + 1 - 1) / 2 = m := by omega
  have hkey : ((2 * m + 1) ^ 2 - 1) / 8 = m * (m + 1) / 2 := by
    have h1 : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    omega
  rw [hhalf, hkey]
  obtain ⟨j, s, hs, rfl⟩ : ∃ j s, s < 4 ∧ m = 4 * j + s :=
    ⟨m / 4, m % 4, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 4).symm⟩
  interval_cases s
  · rw [show (4 * j + 0) * (4 * j + 0 + 1) = 2 * (8 * j ^ 2 + 2 * j) by ring]
    split_ifs <;> omega
  · rw [show (4 * j + 1) * (4 * j + 1 + 1) = 2 * (8 * j ^ 2 + 6 * j + 1) by ring]
    split_ifs <;> omega
  · rw [show (4 * j + 2) * (4 * j + 2 + 1) = 2 * (8 * j ^ 2 + 10 * j + 3) by ring]
    split_ifs <;> omega
  · rw [show (4 * j + 3) * (4 * j + 3 + 1) = 2 * (8 * j ^ 2 + 14 * j + 6) by ring]
    split_ifs <;> omega

/-- The supplement value as a signed power: `(-1)^((n-1)/2 + (n²-1)/8)` is `+1`
    for `n ≡ 1, 3 (mod 8)` and `-1` for `n ≡ 5, 7 (mod 8)`. -/
theorem neg_one_pow_exponent (hodd : Odd n) :
    (-1 : ℤ) ^ ((n - 1) / 2 + (n ^ 2 - 1) / 8)
      = if n % 8 = 1 ∨ n % 8 = 3 then 1 else -1 := by
  have hpar := exponent_parity hodd
  rcases Nat.even_or_odd ((n - 1) / 2 + (n ^ 2 - 1) / 8) with h | h
  · rw [h.neg_one_pow, if_pos]
    have : ((n - 1) / 2 + (n ^ 2 - 1) / 8) % 2 = 0 := Nat.even_iff.mp h
    by_contra hcon; rw [if_neg hcon] at hpar; omega
  · rw [h.neg_one_pow, if_neg]
    have : ((n - 1) / 2 + (n ^ 2 - 1) / 8) % 2 = 1 := Nat.odd_iff.mp h
    intro hcon; rw [if_pos hcon] at hpar; omega

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE THIRD SUPPLEMENT TO QUADRATIC RECIPROCITY
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Third supplementary law of quadratic reciprocity (product form).**
    For every odd `n > 0`, since `-2 = (-1)·2` and the Jacobi symbol is
    multiplicative in its numerator,

        J(-2 | n) = J(-1 | n) · J(2 | n)
                  = (-1)^((n-1)/2) · (-1)^((n²-1)/8). -/
theorem jacobiSym_neg_two (hodd : Odd n) :
    jacobiSym (-2) n = (-1 : ℤ) ^ ((n - 1) / 2) * (-1 : ℤ) ^ ((n ^ 2 - 1) / 8) := by
  rw [show (-2 : ℤ) = -1 * 2 by ring, jacobiSym.mul_left,
    ZolotarevFirstSupplement.jacobiSym_neg_one hodd,
    ZolotarevSecondSupplement.jacobiSym_two hodd]

/-- **Third supplement (single power form).**
    `J(-2 | n) = (-1)^((n-1)/2 + (n²-1)/8)` for odd `n`. -/
theorem jacobiSym_neg_two_pow (hodd : Odd n) :
    jacobiSym (-2) n = (-1 : ℤ) ^ ((n - 1) / 2 + (n ^ 2 - 1) / 8) := by
  rw [jacobiSym_neg_two hodd, ← pow_add]

/-- **Closed-form power formula for `χ₈'`.**  For every odd `n`,

        χ₈' n = (-1) ^ ((n-1)/2 + (n²-1)/8).

    Mathlib supplies only the mod-8 case split `χ₈'_nat_eq_if_mod_eight`; this is
    the explicit power form, the octic analogue of `ZMod.χ₄_eq_neg_one_pow` and
    the companion of the second supplement's `χ₈` power form. -/
theorem chi8'_eq_neg_one_pow (hodd : Odd n) :
    ZMod.χ₈' (n : ZMod 8) = (-1 : ℤ) ^ ((n - 1) / 2 + (n ^ 2 - 1) / 8) := by
  rw [ZMod.χ₈'_nat_eq_if_mod_eight, neg_one_pow_exponent hodd,
    if_neg (by simp [Nat.odd_iff.mp hodd])]

/-- **Consistency with Mathlib's `jacobiSym.at_neg_two`.**  The Zolotarev
    evaluation `(-1)^((n-1)/2 + (n²-1)/8)` agrees with Mathlib's character value
    `J(-2 | n) = χ₈' n`. -/
theorem jacobiSym_neg_two_eq_chi8' (hodd : Odd n) :
    (-1 : ℤ) ^ ((n - 1) / 2 + (n ^ 2 - 1) / 8) = ZMod.χ₈' (n : ZMod 8) := by
  rw [← jacobiSym_neg_two_pow hodd, jacobiSym.at_neg_two hodd]

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: THE RESIDUE CRITERION  (-2 is a QR ⇔ n ≡ 1, 3 mod 8)
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The third supplement in explicit residue form.**  For odd `n`,

        J(-2 | n) = if n ≡ 1, 3 (mod 8) then 1 else -1. -/
theorem jacobiSym_neg_two_residue (hodd : Odd n) :
    jacobiSym (-2) n = if n % 8 = 1 ∨ n % 8 = 3 then 1 else -1 := by
  rw [jacobiSym_neg_two_pow hodd, neg_one_pow_exponent hodd]

/-- **The classical criterion for `-2` to be a quadratic residue.**  For odd `n`,

        J(-2 | n) = 1   ⇔   n ≡ 1, 3 (mod 8).

    (For an odd prime `p` this is the statement that `-2` is a quadratic residue
    mod `p` iff `p ≡ 1, 3 (mod 8)`, equivalently `p` is represented by `x² + 2y²`.) -/
theorem jacobiSym_neg_two_eq_one_iff (hodd : Odd n) :
    jacobiSym (-2) n = 1 ↔ n % 8 = 1 ∨ n % 8 = 3 := by
  rw [jacobiSym_neg_two_residue hodd]
  split_ifs with h
  · simp [h]
  · constructor
    · intro hc; norm_num at hc
    · intro hc; exact absurd hc h

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: THE ZOLOTAREV PERMUTATION-SIGN READING
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **The `x ↦ (-2)·x` permutation sign.**  For odd `n` and any unit
    `u : (ℤ/n)ˣ` whose underlying residue is `-2`, the sign of the Zolotarev
    permutation `x ↦ u·x` on the whole ring `ℤ/n` is

        sign(ringMulPerm u) = (-1) ^ ((n-1)/2 + (n²-1)/8),

    read off via the full-odd Frobenius identity `sign(ringMulPerm u) = J(-2 | n)`. -/
theorem sign_ringMulPerm_neg_two (hodd : Odd n) (u : (ZMod n)ˣ) (hu : (u : ZMod n) = -2) :
    (Equiv.Perm.sign (ringMulPerm u) : ℤ) = (-1 : ℤ) ^ ((n - 1) / 2 + (n ^ 2 - 1) / 8) := by
  have hA : ((-2 : ℤ) : ZMod n) = (u : ZMod n) := by rw [hu]; norm_cast
  rw [ZolotarevFullOdd.sign_ringMulPerm_eq_jacobiSym_odd hodd u (-2) hA,
    jacobiSym_neg_two_pow hodd]

/-
═══════════════════════════════════════════════════════════════════════════════
PART V: THE LEGENDRE (ODD-PRIME) SPECIAL CASE
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Third supplement for the Legendre symbol.**  For an odd prime `p`,

        (-2 / p) = (-1) ^ ((p-1)/2 + (p²-1)/8),

    obtained by specializing the Jacobi-symbol supplement to a prime modulus. -/
theorem legendreSym_neg_two (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-2) = (-1 : ℤ) ^ ((p - 1) / 2 + (p ^ 2 - 1) / 8) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  rw [jacobiSym.legendreSym.to_jacobiSym,
    jacobiSym_neg_two_pow ((Fact.out : p.Prime).odd_of_ne_two hp)]

/-- **`-2` is a quadratic residue criterion at an odd prime.**

        (-2 / p) = 1   ⇔   p ≡ 1, 3 (mod 8). -/
theorem legendreSym_neg_two_eq_one_iff (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    legendreSym p (-2) = 1 ↔ p % 8 = 1 ∨ p % 8 = 3 := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩
  rw [jacobiSym.legendreSym.to_jacobiSym]
  exact jacobiSym_neg_two_eq_one_iff ((Fact.out : p.Prime).odd_of_ne_two hp)

end ZolotarevThirdSupplement

#check @ZolotarevThirdSupplement.jacobiSym_neg_two_pow
#check @ZolotarevThirdSupplement.chi8'_eq_neg_one_pow
#check @ZolotarevThirdSupplement.jacobiSym_neg_two_eq_one_iff
#check @ZolotarevThirdSupplement.sign_ringMulPerm_neg_two
#check @ZolotarevThirdSupplement.legendreSym_neg_two_eq_one_iff
