/-
  # The Algebraic Numbers Form a Perfect Field — No Inseparable Extensions

  The parent file (`AlgebraicNumbersCountableOQ01OQ01`) realizes the algebraic numbers
  concretely as `algebraicNumbersField : IntermediateField ℚ ℂ` and proves it is an
  **algebraically closed** field — an algebraic closure of `ℚ` sitting inside `ℂ`.

  This file adds the *separability* half of the picture, answering the open question:
  formalize that `ℚ̄` is **perfect**, so every algebraic extension of `ℚ` is separable,
  and conclude that `algebraicClosure ℚ ℂ` has **no inseparable extensions**.

  ## What is proved

  1. **`ℚ` is perfect.** A field of characteristic zero is perfect
     (`PerfectField.ofCharZero`), so `PerfectField ℚ` holds. Consequently every
     algebraic extension `E / ℚ` is a *separable* extension
     (`Algebra.IsAlgebraic.isSeparable_of_perfectField`), and the minimal polynomial
     over `ℚ` of any algebraic number is separable — hence squarefree, with distinct
     roots.

  2. **`ℚ̄` is perfect, two ways.** The field of algebraic numbers is perfect for two
     independent reasons: it is *algebraically closed* (so perfect by the general
     `IsAlgClosed → PerfectField`), and it is an *algebraic extension of the perfect
     field `ℚ`* (so perfect by `Algebra.IsAlgebraic.perfectField`). The algebraic
     numbers are themselves a separable extension of `ℚ`.

  3. **No inseparable extensions.** Because `ℚ̄` is perfect, *every* algebraic extension
     `L / ℚ̄` is separable: the algebraic closure of `ℚ` admits no inseparable algebraic
     extension. The same holds verbatim for Mathlib's `algebraicClosure ℚ ℂ`.

  4. **Counting embeddings of a number field.** As a concrete arithmetic payoff,
     separability forces the separable degree to equal the full degree: for a finite
     extension `E / ℚ`, `finSepDegree ℚ E = [E : ℚ]`. Unwinding the definition of
     separable degree, this says a number field of degree `n` has exactly `n`
     embeddings into its algebraic closure — the classical statement that a degree-`n`
     number field has `n` complex embeddings.

  Tags: field-theory, algebraic-numbers, perfect-field, separability, separable-degree,
        number-field, embeddings, characteristic-zero
-/
import Proofs.AlgebraicNumbersCountableOQ01OQ01
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.Tactic

open AlgebraicNumbersCountableOQ01OQ01

namespace AlgebraicNumbersCountableOQ01OQ01OQ01

/- ============================================================
   § 1 : ℚ is perfect; its algebraic extensions are separable
   ============================================================ -/

/-- `ℚ` is a **perfect field**: every field of characteristic zero is perfect
    (`PerfectField.ofCharZero`). -/
theorem perfectField_rat : PerfectField ℚ := inferInstance

/-- **Every algebraic extension of `ℚ` is separable.** Since `ℚ` is perfect, any
    algebraic extension `E / ℚ` is automatically a separable extension. -/
theorem isSeparable_of_isAlgebraic_rat {E : Type*} [Field E] [Algebra ℚ E]
    [Algebra.IsAlgebraic ℚ E] : Algebra.IsSeparable ℚ E := inferInstance

/-- The minimal polynomial over `ℚ` of any algebraic number is **separable** (it has no
    repeated roots) — the polynomial-level face of `ℚ` being perfect. -/
theorem minpoly_separable_rat {E : Type*} [Field E] [Algebra ℚ E] (x : E)
    (hx : IsIntegral ℚ x) : (minpoly ℚ x).Separable :=
  PerfectField.separable_of_irreducible (minpoly.irreducible hx)

/-- Consequently, the minimal polynomial over `ℚ` of any algebraic number is squarefree. -/
theorem minpoly_squarefree_rat {E : Type*} [Field E] [Algebra ℚ E] (x : E)
    (hx : IsIntegral ℚ x) : Squarefree (minpoly ℚ x) :=
  (minpoly_separable_rat x hx).squarefree

/- ============================================================
   § 2 : The algebraic numbers ℚ̄ ⊆ ℂ form a perfect field
   ============================================================ -/

/-- **`ℚ̄` is perfect (via algebraic closedness).** The field of algebraic numbers is
    algebraically closed (parent result), and every algebraically closed field is
    perfect. -/
theorem perfectField_algebraicNumbers : PerfectField algebraicNumbersField :=
  inferInstance

/-- **`ℚ̄` is perfect (via being algebraic over `ℚ`).** A second, independent argument:
    `ℚ̄ / ℚ` is an algebraic extension of the perfect field `ℚ`, and an algebraic
    extension of a perfect field is perfect (`Algebra.IsAlgebraic.perfectField`). -/
theorem perfectField_algebraicNumbers_of_algebraic :
    PerfectField algebraicNumbersField :=
  Algebra.IsAlgebraic.perfectField (K := ℚ)

/-- The algebraic numbers are a **separable** extension of `ℚ`: every algebraic number
    is separable over `ℚ`. -/
theorem isSeparable_rat_algebraicNumbers :
    Algebra.IsSeparable ℚ algebraicNumbersField := inferInstance

/- ============================================================
   § 3 : No inseparable extensions of ℚ̄
   ============================================================ -/

/-- **No inseparable extensions.** Every algebraic extension `L` of the field of
    algebraic numbers is separable — `ℚ̄` admits no inseparable algebraic extension.
    (Of course `ℚ̄` is algebraically closed, so such an `L` is even trivial; the point
    is that separability holds for *any* algebraic `L / ℚ̄`, a property of perfectness
    that does not require algebraic closedness.) -/
theorem isSeparable_of_isAlgebraic_algebraicNumbers {L : Type*} [Field L]
    [Algebra algebraicNumbersField L] [Algebra.IsAlgebraic algebraicNumbersField L] :
    Algebra.IsSeparable algebraicNumbersField L := inferInstance

/-- The same conclusion phrased for Mathlib's relative algebraic closure
    `algebraicClosure ℚ ℂ`, which coincides with the algebraic numbers
    (`algebraicNumbersField_eq`): it is a perfect field with no inseparable extensions. -/
theorem perfectField_algebraicClosure_rat_complex :
    PerfectField (algebraicClosure ℚ ℂ) := inferInstance

/- ============================================================
   § 4 : Counting embeddings of a number field
   ============================================================ -/

/-- **Separable degree equals degree for number fields.** For any finite extension
    `E / ℚ`, separability (which holds automatically, `ℚ` being perfect) forces the
    separable degree to equal the full degree. -/
theorem finSepDegree_eq_finrank_rat {E : Type*} [Field E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] : Field.finSepDegree ℚ E = Module.finrank ℚ E := by
  haveI : Algebra.IsAlgebraic ℚ E := Algebra.IsAlgebraic.of_finite ℚ E
  exact Field.finSepDegree_eq_finrank_of_isSeparable ℚ E

/-- **A number field of degree `n` has exactly `n` embeddings.** Unfolding the
    definition of separable degree (`finSepDegree ℚ E = Nat.card (Field.Emb ℚ E)`),
    the previous theorem says the number of `ℚ`-algebra embeddings of a finite extension
    `E` into its algebraic closure equals `[E : ℚ]`. -/
theorem card_emb_eq_finrank_rat {E : Type*} [Field E] [Algebra ℚ E]
    [FiniteDimensional ℚ E] : Nat.card (Field.Emb ℚ E) = Module.finrank ℚ E :=
  finSepDegree_eq_finrank_rat

section Examples

-- Every algebraic number's minimal polynomial over `ℚ` is squarefree.
example {z : ℂ} (hz : IsAlgebraic ℚ z) : Squarefree (minpoly ℚ z) :=
  minpoly_squarefree_rat z hz.isIntegral

-- The algebraic numbers are a separable (indeed perfect) extension of `ℚ`.
example : Algebra.IsSeparable ℚ algebraicNumbersField := isSeparable_rat_algebraicNumbers

end Examples

end AlgebraicNumbersCountableOQ01OQ01OQ01
