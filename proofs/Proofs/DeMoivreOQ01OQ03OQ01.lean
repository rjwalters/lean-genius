/-
# Chebyshev–De Moivre for all integer indices `n ∈ ℤ`
  (de-moivre-oq-01-oq-03-oq-01)

## Open Question (OQ-01 of de-moivre-oq-01-oq-03)
The parent established the algebraic De Moivre–Chebyshev identity
  `(C R n).eval (z + w) = zⁿ + wⁿ`     whenever `z · w = 1`,
but only for **natural** indices `n : ℕ`.  The Chebyshev polynomial of the third
kind `C` is, however, indexed by all of `ℤ` in Mathlib, and the symmetry
`C R (-n) = C R n` (`Polynomial.Chebyshev.C_neg`) strongly suggests the identity
should close up under negation.  Does it?

## Answer: YES — and the extension is *forced* by the `z·w = 1` constraint.

On the "unit circle" `z · w = 1` we have `w = z⁻¹` and `z = w⁻¹`, so the two-sided
power map `m ↦ zᵐ` (now with `m : ℤ`) sends `-m` to `(zᵐ)⁻¹ = wᵐ`.  Combined with
`C R (-n) = C R n`, the negative-index identity reduces to the positive one with the
roles of `z` and `w` swapped:

      `(C R (-m)).eval (z + w) = (C R m).eval (z + w) = zᵐ + wᵐ = w⁻ᵐ + z⁻ᵐ`.

We package this two ways:

* **Units form** over an arbitrary `CommRing R`: for `z : Rˣ` and `n : ℤ`,
      `(C R n).eval (z + z⁻¹) = ↑(zⁿ) + ↑(z⁻ⁿ)`,
  where `zⁿ : Rˣ` is the genuine ℤ-power in the unit group.  This is the sharpest
  statement: it needs no division and no field structure.
* **Field form**: for any field `F`, `z ≠ 0`, and `n : ℤ`,
      `(C F n).eval (z + z⁻¹) = zⁿ + (z⁻¹)ⁿ`     (`zⁿ` = `zpow`).
  Specializes for free to finite fields `ZMod p`, the p-adics `ℚ_[p]`, ℝ and ℂ.

This is the integer-index closure of the parent's de Moivre identity: the power map
`z ↦ zⁿ` is conjugate to evaluation of a fixed integer-indexed polynomial for *every*
`n ∈ ℤ`, positive, zero, or negative.

## Status
- All theorems proved (0 sorries, 0 axioms, no `native_decide`).
- Reuses the parent's natural-index engine `chebyshevC_eval_field`; the only new
  ingredient is `Chebyshev.C_neg` plus `zpow` bookkeeping.
- Builds on `Mathlib.RingTheory.Polynomial.Chebyshev` and the parent file.
-/

import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Tactic
import Proofs.DeMoivreOQ01OQ03

namespace DeMoivreChebyshevIntegerIndex

open Polynomial.Chebyshev
open DeMoivreChebyshevFiniteField

/-
═══════════════════════════════════════════════════════════════════════════════
PART I: THE FIELD IDENTITY FOR ALL `n ∈ ℤ`
═══════════════════════════════════════════════════════════════════════════════ -/

variable {F : Type*} [Field F]

/-- **Integer-index De Moivre–Chebyshev identity (field form).**
    In any field `F`, for `z ≠ 0` and *every* integer `n : ℤ`,
      `(C F n).eval (z + z⁻¹) = zⁿ + (z⁻¹)ⁿ`,
    where `zⁿ` denotes the `ℤ`-power (`zpow`).  This extends the parent's
    natural-index identity `chebyshevC_eval_field` to all of `ℤ`, using the
    Chebyshev symmetry `C F (-n) = C F n`. -/
theorem chebyshevC_eval_field_int (z : F) (hz : z ≠ 0) (n : ℤ) :
    (C F n).eval (z + z⁻¹) = z ^ n + (z⁻¹) ^ n := by
  -- Split into `n ≥ 0` and `n < 0`.
  rcases le_or_gt 0 n with hn | hn
  · -- Nonnegative: lift `n` to a natural number and invoke the parent identity.
    lift n to ℕ using hn with k
    rw [zpow_natCast, zpow_natCast]
    exact_mod_cast chebyshevC_eval_field z hz k
  · -- Negative: write `n = -m` with `m = -n > 0`, use `C_neg` to flip the index.
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) :=
      ⟨(-n).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
    -- On the unit circle the negative powers fold back: `z^(-m) = (z⁻¹)^m`, etc.
    have h1 : z ^ (-(m : ℤ)) = (z⁻¹) ^ m := by
      rw [zpow_neg, zpow_natCast, ← inv_pow]
    have h2 : (z⁻¹) ^ (-(m : ℤ)) = z ^ m := by
      rw [zpow_neg, zpow_natCast, ← inv_pow, inv_inv]
    rw [C_neg, chebyshevC_eval_field z hz m, h1, h2]
    ring

/-
═══════════════════════════════════════════════════════════════════════════════
PART II: THE UNITS IDENTITY OVER AN ARBITRARY COMMUTATIVE RING
═══════════════════════════════════════════════════════════════════════════════ -/

variable {R : Type*} [CommRing R]

/-- **Integer-index De Moivre–Chebyshev identity (units form).**
    For any commutative ring `R`, any unit `z : Rˣ`, and *every* integer `n : ℤ`,
      `(C R n).eval (↑z + ↑z⁻¹) = ↑(zⁿ) + ↑(z⁻ⁿ)`,
    where `zⁿ : Rˣ` is the genuine `ℤ`-power in the unit group.  This is the
    division-free sharpening of the field form: it holds over *any* `CommRing`. -/
theorem chebyshevC_eval_units_int (z : Rˣ) (n : ℤ) :
    (C R n).eval ((z : R) + (↑z⁻¹ : R)) = (↑(z ^ n) : R) + (↑(z ^ (-n)) : R) := by
  -- Coercion of the genuine ℤ-power in `Rˣ` to `R`, matched against the parent's
  -- ℕ-indexed identity in both sign branches.
  rcases le_or_gt 0 n with hn | hn
  · -- Nonnegative index.
    lift n to ℕ using hn with k
    have h1 : (↑(z ^ (k : ℤ)) : R) = (z : R) ^ k := by
      rw [zpow_natCast, Units.val_pow_eq_pow_val]
    have h2 : (↑(z ^ (-(k : ℤ))) : R) = (↑z⁻¹ : R) ^ k := by
      rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
    rw [h1, h2]
    exact chebyshevC_eval_add (z : R) (↑z⁻¹ : R) z.mul_inv k
  · -- Negative index: `n = -m`, flip the polynomial index via `C_neg`.
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) :=
      ⟨(-n).toNat, by rw [Int.toNat_of_nonneg (by omega)]; ring⟩
    have h1 : (↑(z ^ (-(m : ℤ))) : R) = (↑z⁻¹ : R) ^ m := by
      rw [zpow_neg, zpow_natCast, ← inv_pow, Units.val_pow_eq_pow_val]
    have h2 : (↑(z ^ (-(-(m : ℤ)))) : R) = (z : R) ^ m := by
      rw [neg_neg, zpow_natCast, Units.val_pow_eq_pow_val]
    rw [C_neg, h1, h2, chebyshevC_eval_add (z : R) (↑z⁻¹ : R) z.mul_inv m]
    ring

/-
═══════════════════════════════════════════════════════════════════════════════
PART III: SPECIALIZATIONS — finite fields and p-adics, now over ℤ
═══════════════════════════════════════════════════════════════════════════════ -/

/-- **Finite-field form (all `n ∈ ℤ`).** For a prime `p`, nonzero `z : ZMod p`,
    and any integer `n`, `(C (ZMod p) n).eval (z + z⁻¹) = zⁿ + (z⁻¹)ⁿ`. -/
theorem chebyshevC_eval_zmod_int (p : ℕ) [Fact p.Prime] (z : ZMod p) (hz : z ≠ 0)
    (n : ℤ) :
    (C (ZMod p) n).eval (z + z⁻¹) = z ^ n + (z⁻¹) ^ n :=
  chebyshevC_eval_field_int z hz n

/-- **p-adic form (all `n ∈ ℤ`).** Over `ℚ_[p]`, for `z ≠ 0` and any integer `n`,
    `(C ℚ_[p] n).eval (z + z⁻¹) = zⁿ + (z⁻¹)ⁿ`. -/
theorem chebyshevC_eval_padic_int (p : ℕ) [Fact p.Prime] (z : ℚ_[p]) (hz : z ≠ 0)
    (n : ℤ) :
    (C ℚ_[p] n).eval (z + z⁻¹) = z ^ n + (z⁻¹) ^ n :=
  chebyshevC_eval_field_int z hz n

/-
═══════════════════════════════════════════════════════════════════════════════
PART IV: CONSISTENCY CHECKS
═══════════════════════════════════════════════════════════════════════════════ -/

/-- Negative index over `ℝ`: `C (-1) = X`, so evaluating at `z + z⁻¹` returns
    `z + z⁻¹`, matching `z⁻¹ + z` (the `n = -1` instance). -/
example (z : ℝ) (hz : z ≠ 0) :
    (C ℝ (-1)).eval (z + z⁻¹) = z ^ (-1 : ℤ) + (z⁻¹) ^ (-1 : ℤ) :=
  chebyshevC_eval_field_int z hz (-1)

/-- In `ZMod 7`: `3⁻¹ = 5`, `3 + 3⁻¹ = 1`, and the `n = -2` instance reads
    `C (-2) (1) = 1² − 2 = −1 = 6`, matching `3⁻² + (3⁻¹)⁻² = 5² + 3² = 4 + 2 = 6`.
    (The `[Fact (Nat.Prime 7)]` binder supplies the field structure on `ZMod 7`
    needed to interpret the `ℤ`-power `z ^ (-2 : ℤ)`.) -/
-- A concrete (file-local) primality witness, so the field structure on `ZMod 7`
-- used to interpret the `ℤ`-power `z ^ (-2 : ℤ)` is a closed instance (not a free
-- variable), keeping the `decide` of `3 ≠ 0` kernel-reducible.
private instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

example :
    (C (ZMod 7) (-2)).eval ((3 : ZMod 7) + (3 : ZMod 7)⁻¹)
      = (3 : ZMod 7) ^ (-2 : ℤ) + ((3 : ZMod 7)⁻¹) ^ (-2 : ℤ) := by
  have h3 : (3 : ZMod 7) ≠ 0 := by decide
  exact chebyshevC_eval_zmod_int 7 3 h3 (-2)

/-
═══════════════════════════════════════════════════════════════════════════════
VERIFICATION
═══════════════════════════════════════════════════════════════════════════════ -/

#check @chebyshevC_eval_field_int
#check @chebyshevC_eval_units_int
#check @chebyshevC_eval_zmod_int
#check @chebyshevC_eval_padic_int

end DeMoivreChebyshevIntegerIndex
