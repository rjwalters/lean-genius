/-
  # The Algebraic Numbers are Perfect: ℚ̄ has no Inseparable Extensions

  The parent file (`AlgebraicNumbersCountableOQ01OQ01`) shows that the algebraic
  numbers `algebraicNumbersField : IntermediateField ℚ ℂ` form an *algebraically
  closed* field — the relative algebraic closure of `ℚ` inside `ℂ`, equal to
  Mathlib's `algebraicClosure ℚ ℂ`, and countable (grandparent result).

  This file settles the natural follow-up: **separability**. In characteristic
  zero every field is *perfect* (`PerfectField.ofCharZero`), so:

  1. every irreducible polynomial over `ℚ` is separable;
  2. every algebraic extension `L / ℚ` is separable (`Algebra.IsSeparable ℚ L`);
  3. the algebraic numbers `ℚ̄` are themselves a perfect field — being algebraic
     over the perfect field `ℚ` — and hence have **no inseparable extensions**:
     every algebraic extension of `ℚ̄` is separable.

  ## What is proved

  * **Characteristic-zero dictionary.** For a char-0 base field `F`, an element of
    an extension is *separable* over `F` iff it is *algebraic* over `F`
    (`isSeparable_iff_isAlgebraic`). Separability is therefore no restriction at all
    in characteristic zero.

  * **Every algebraic extension of a char-0 field is separable and perfect.**
    `isSeparable_of_charZero`, `perfectField_of_charZero` package Mathlib's
    `Algebra.IsAlgebraic.isSeparable_of_perfectField` / `.perfectField` through the
    `PerfectField.ofCharZero` instance.

  * **ℚ̄ is perfect.** `instance : PerfectField algebraicNumbersField`, obtained as
    "algebraic over the perfect field `ℚ`" — the reasoning the open question asks for.

  * **No inseparable extensions of ℚ̄.** `isSeparable_of_isAlgebraic_algebraicNumbersField`:
    any algebraic extension of `ℚ̄` is separable over `ℚ̄`.

  * **Concrete equality of closures.** The separable closure of `ℚ` in `ℂ` coincides
    with its algebraic closure (`separableClosure_rat_eq_algebraicClosure`), and hence
    with the concrete field of algebraic numbers
    (`separableClosure_rat_eq_algebraicNumbersField`). There is genuinely no purely
    inseparable content sitting between the separable and algebraic closures of `ℚ`.

  * **Separably closed.** As an algebraically closed field, `ℚ̄` is separably closed
    (`instance : IsSepClosed algebraicNumbersField`).

  Tags: field-theory, algebraic-numbers, perfect-field, separability,
        separable-closure, characteristic-zero
-/
import Proofs.AlgebraicNumbersCountableOQ01OQ01
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Tactic

open Polynomial AlgebraicNumbersCountableOQ01OQ01

namespace AlgebraicNumbersCountableOQ01OQ01OQ01

/- ============================================================
   § 1 : Characteristic-zero dictionary — separable = algebraic
   ============================================================ -/

variable (F L : Type*) [Field F] [Field L] [Algebra F L]

/-- **Separable = algebraic in characteristic zero.** Over a characteristic-zero base
    field, an element of an extension is separable iff it is algebraic. The minimal
    polynomial of an algebraic (hence integral) element is irreducible, and in
    characteristic zero irreducible polynomials are separable
    (`Irreducible.separable`); conversely separability forces integrality, hence
    algebraicity. -/
theorem isSeparable_iff_isAlgebraic [CharZero F] {x : L} :
    IsSeparable F x ↔ IsAlgebraic F x := by
  constructor
  · intro h
    exact h.isIntegral.isAlgebraic
  · intro h
    have hi : IsIntegral F x := h.isIntegral
    exact (minpoly.irreducible hi).separable

/-- **Every algebraic extension of a characteristic-zero field is separable.**
    Characteristic-zero fields are perfect (`PerfectField.ofCharZero`), and algebraic
    extensions of a perfect field are separable. -/
instance isSeparable_of_charZero [CharZero F] [Algebra.IsAlgebraic F L] :
    Algebra.IsSeparable F L :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- **Every algebraic extension of a characteristic-zero field is itself perfect.** -/
theorem perfectField_of_charZero [CharZero F] [Algebra.IsAlgebraic F L] :
    PerfectField L :=
  Algebra.IsAlgebraic.perfectField (K := F)

/- ============================================================
   § 2 : ℚ — every algebraic extension is separable
   ============================================================ -/

/-- **Every algebraic extension of `ℚ` is separable.** This is the concrete instance of
    the characteristic-zero phenomenon for the rationals. -/
theorem isSeparable_of_isAlgebraic_rat (M : Type*) [Field M] [Algebra ℚ M]
    [Algebra.IsAlgebraic ℚ M] : Algebra.IsSeparable ℚ M :=
  isSeparable_of_charZero ℚ M

/-- A complex number that is algebraic over `ℚ` is separable over `ℚ`: its minimal
    polynomial has no repeated roots. -/
theorem isSeparable_of_isAlgebraic_complex {z : ℂ} (hz : IsAlgebraic ℚ z) :
    IsSeparable ℚ z :=
  (isSeparable_iff_isAlgebraic ℚ ℂ).mpr hz

/-- The minimal polynomial over `ℚ` of any algebraic number is squarefree. -/
theorem minpoly_squarefree_of_isAlgebraic {z : ℂ} (hz : IsAlgebraic ℚ z) :
    Squarefree (minpoly ℚ z) :=
  (isSeparable_of_isAlgebraic_complex hz).squarefree

/- ============================================================
   § 3 : ℚ̄ is perfect and has no inseparable extensions
   ============================================================ -/

/-- **The algebraic numbers `ℚ̄` form a perfect field.** They are algebraic over the
    perfect field `ℚ`, so by transitivity of perfectness under algebraic extensions
    (`Algebra.IsAlgebraic.perfectField`) the field `ℚ̄` is itself perfect. -/
instance : PerfectField algebraicNumbersField :=
  Algebra.IsAlgebraic.perfectField (K := ℚ)

/-- Every irreducible polynomial over `ℚ̄` is separable — the defining property of a
    perfect field, here for the algebraic numbers. -/
theorem separable_of_irreducible_over_algebraicNumbersField
    {f : (algebraicNumbersField)[X]} (hf : Irreducible f) : f.Separable :=
  PerfectField.separable_of_irreducible hf

/-- **ℚ̄ has no inseparable extensions.** Any algebraic extension of the algebraic
    numbers is separable over them, because `ℚ̄` is perfect. -/
instance isSeparable_of_isAlgebraic_algebraicNumbersField (M : Type*) [Field M]
    [Algebra algebraicNumbersField M] [Algebra.IsAlgebraic algebraicNumbersField M] :
    Algebra.IsSeparable algebraicNumbersField M :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

/-- `ℚ̄` is separable over `ℚ`: every algebraic number is a separable element. -/
instance : Algebra.IsSeparable ℚ algebraicNumbersField :=
  isSeparable_of_charZero ℚ algebraicNumbersField

/- ============================================================
   § 4 : The separable closure of ℚ in ℂ equals its algebraic closure
   ============================================================ -/

/-- **No purely inseparable content over `ℚ`.** The separable closure of `ℚ` inside
    `ℂ` coincides with its algebraic closure: because `ℚ` has characteristic zero,
    *every* algebraic number is already separable, so the two closures agree. -/
theorem separableClosure_rat_eq_algebraicClosure :
    separableClosure ℚ ℂ = algebraicClosure ℚ ℂ := by
  ext x
  rw [mem_separableClosure_iff, mem_algebraicClosure_iff]
  exact isSeparable_iff_isAlgebraic ℚ ℂ

/-- The separable closure of `ℚ` in `ℂ` is exactly the concrete field of algebraic
    numbers built in the parent file. -/
theorem separableClosure_rat_eq_algebraicNumbersField :
    separableClosure ℚ ℂ = algebraicNumbersField := by
  rw [separableClosure_rat_eq_algebraicClosure, algebraicNumbersField_eq]

/-- **ℚ̄ is separably closed.** Being algebraically closed (parent result), the field of
    algebraic numbers is in particular separably closed: it admits no nontrivial
    separable algebraic extension. -/
instance : IsSepClosed algebraicNumbersField :=
  IsSepClosed.of_isAlgClosed _

section Examples

-- The separable and algebraic closures of `ℚ` in `ℂ` are the same object.
example : separableClosure ℚ ℂ = algebraicClosure ℚ ℂ :=
  separableClosure_rat_eq_algebraicClosure

-- Every algebraic extension of `ℚ̄` is separable (no inseparable extensions).
example (M : Type*) [Field M] [Algebra algebraicNumbersField M]
    [Algebra.IsAlgebraic algebraicNumbersField M] :
    Algebra.IsSeparable algebraicNumbersField M := inferInstance

-- `ℚ̄` is perfect: every irreducible polynomial over it is separable.
example {f : (algebraicNumbersField)[X]} (hf : Irreducible f) : f.Separable :=
  PerfectField.separable_of_irreducible hf

end Examples

end AlgebraicNumbersCountableOQ01OQ01OQ01
