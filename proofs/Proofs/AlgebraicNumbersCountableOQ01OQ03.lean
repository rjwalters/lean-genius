/-
  # The Field of Algebraic Numbers as `AlgebraicClosure ℚ` — and its Countability

  The parent gallery proof (`AlgebraicNumbersCountable`) shows the algebraic numbers
  `{x : ℂ | IsAlgebraic ℚ x}` form a *countable set*, and its leaf
  `AlgebraicNumbersCountableOQ01` upgrades that set to a *bespoke* `Subfield ℂ`
  (`algebraicSubfield ℚ ℂ`) using the closure-under-arithmetic facts.

  This leaf (OQ-01 → OQ-03) closes the loop with Mathlib's own field-theoretic
  picture and extracts the genuinely new payoff:

  ## 1. Identification with Mathlib's relative algebraic closure

  Mathlib packages the algebraic numbers as `algebraicClosure ℚ ℂ : IntermediateField ℚ ℂ`
  (the relative algebraic closure of `ℚ` inside `ℂ`). We record that this
  `IntermediateField` has exactly the parent's carrier
  `{x : ℂ | IsAlgebraic ℚ x}` (`Qbar_carrier`), so the bespoke `Subfield` of OQ-01 and
  Mathlib's `IntermediateField` describe the same object.

  ## 2. It is algebraically closed, and it *is* an algebraic closure of `ℚ`

  Because `ℂ` is algebraically closed, Mathlib gives `IsAlgClosed (algebraicClosure ℚ ℂ)`
  and `IsAlgClosure ℚ (algebraicClosure ℚ ℂ)` for free. Uniqueness of algebraic
  closures (`IsAlgClosure.equiv`) then yields a `ℚ`-algebra isomorphism
  `AlgebraicClosure ℚ ≃ₐ[ℚ] algebraicClosure ℚ ℂ` (`equivAlgebraicClosureRat`),
  identifying the abstract `AlgebraicClosure ℚ` with the concrete algebraic numbers.

  ## 3. The new result: `AlgebraicClosure ℚ` is countable

  Mathlib does **not** record that the abstract `AlgebraicClosure ℚ` is countable
  (it is built by a transfinite `MvPolynomial`/quotient tower with no a-priori
  cardinality bound). Transporting the parent's countability of the algebraic
  numbers across the isomorphism of §2 supplies it:

      `Countable (AlgebraicClosure ℚ)`              (`countable_algebraicClosure_rat`)

  and in fact it is countably infinite — `#(AlgebraicClosure ℚ) = ℵ₀`
  (`cardinalMk_algebraicClosure_rat`). The same transport works over any countable
  base field of characteristic zero (`countable_algebraicClosure` for a general
  countable field with a chosen algebraically closed extension).

  The mathematical content is entirely in §3: §1–§2 are the bridge that lets the
  parent's set-level countability become a statement about the *field* objects that
  the rest of the algebra library actually uses.

  Tags: field-theory, algebraic-numbers, algebraic-closure, countability,
        cardinal-arithmetic, intermediate-field
-/
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Basic
import Mathlib.Tactic

namespace AlgebraicNumbersCountableOQ01OQ03

open scoped Cardinal

/- ============================================================
   § 1 : The algebraic numbers as Mathlib's relative algebraic closure
   ============================================================ -/

/-- The field of algebraic numbers, packaged as Mathlib's relative algebraic closure
of `ℚ` inside `ℂ`. This is the `IntermediateField` version of the bespoke
`algebraicSubfield ℚ ℂ : Subfield ℂ` from the sibling leaf `…OQ01`. -/
noncomputable abbrev Qbar : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

/-- `Qbar` carries exactly the parent proof's set of algebraic numbers, so the
bespoke `Subfield` of OQ-01 and this `IntermediateField` describe the same object. -/
theorem Qbar_carrier : (Qbar : Set ℂ) = {x : ℂ | IsAlgebraic ℚ x} := by
  ext x
  exact mem_algebraicClosure_iff

/- ============================================================
   § 2 : `Qbar` is an algebraic closure of `ℚ`
   ============================================================ -/

/-- `Qbar` is algebraically closed (`ℂ` is, and the relative algebraic closure of a
field inside an algebraically closed field is algebraically closed). -/
instance : IsAlgClosed Qbar := IsAlgClosure.isAlgClosed ℚ

/-- `Qbar` is an algebraic closure of `ℚ`: it is algebraically closed and algebraic
over `ℚ`. -/
example : IsAlgClosure ℚ Qbar := inferInstance

/-- **Identification with the abstract algebraic closure.** Uniqueness of algebraic
closures gives a `ℚ`-algebra isomorphism between the abstractly-constructed
`AlgebraicClosure ℚ` and the concrete field of algebraic numbers `Qbar ⊆ ℂ`. -/
noncomputable def equivAlgebraicClosureRat : AlgebraicClosure ℚ ≃ₐ[ℚ] Qbar :=
  IsAlgClosure.equiv ℚ (AlgebraicClosure ℚ) Qbar

/- ============================================================
   § 3 : Countability — the new content
   ============================================================ -/

/-- The concrete algebraic numbers `Qbar ⊆ ℂ` form a countable type (the parent's
set-level countability, recast for the subtype). -/
instance : Countable Qbar := by
  have hset : Set.Countable (Qbar : Set ℂ) := by
    rw [Qbar_carrier]; exact Algebraic.countable ℚ ℂ
  exact hset.to_subtype

/-- **`AlgebraicClosure ℚ` is countable.** Mathlib builds `AlgebraicClosure ℚ` by a
transfinite tower with no a-priori cardinality bound; transporting the countability
of the concrete algebraic numbers across `equivAlgebraicClosureRat` supplies it. -/
instance countable_algebraicClosure_rat : Countable (AlgebraicClosure ℚ) :=
  Countable.of_equiv Qbar equivAlgebraicClosureRat.toEquiv.symm

/-- `AlgebraicClosure ℚ` is countably infinite: its cardinality is exactly `ℵ₀`. -/
theorem cardinalMk_algebraicClosure_rat : #(AlgebraicClosure ℚ) = ℵ₀ := by
  -- `≤ ℵ₀` from countability (§3), `≥ ℵ₀` from being an infinite (characteristic-zero) field.
  have hle : #(AlgebraicClosure ℚ) ≤ ℵ₀ := Cardinal.mk_le_aleph0
  have hge : ℵ₀ ≤ #(AlgebraicClosure ℚ) := Cardinal.aleph0_le_mk _
  exact le_antisymm hle hge

/- ============================================================
   § 4 : The general statement over an arbitrary countable base field
   ============================================================ -/

section General

variable (F E : Type*) [Field F] [Field E] [Algebra F E] [IsAlgClosed E] [Countable F]

/-- For any countable field `F` with a chosen algebraically closed extension `E`, the
relative algebraic closure of `F` in `E` is countable. This is the base-field-agnostic
form of §3: the algebraic elements over a countable field form a countable set, and the
`IntermediateField` is the subtype on that set. -/
instance : Countable (algebraicClosure F E) := by
  have hset : Set.Countable ((algebraicClosure F E : IntermediateField F E) : Set E) := by
    have : ((algebraicClosure F E : IntermediateField F E) : Set E)
        = {x : E | IsAlgebraic F x} := by
      ext x; exact mem_algebraicClosure_iff
    rw [this]; exact Algebraic.countable F E
  exact hset.to_subtype

end General

/-- **`AlgebraicClosure F` is countable for any countable field `F`.** Transport the
countability of the relative algebraic closure (inside any algebraically closed
extension `E`) across the uniqueness isomorphism of algebraic closures. -/
theorem countable_algebraicClosure (F E : Type*) [Field F] [Field E] [Algebra F E]
    [IsAlgClosed E] [Countable F] : Countable (AlgebraicClosure F) :=
  Countable.of_equiv (algebraicClosure F E)
    (IsAlgClosure.equiv F (AlgebraicClosure F) (algebraicClosure F E)).toEquiv.symm

/- ============================================================
   § 5 : Sanity checks
   ============================================================ -/

section Examples

-- The isomorphism is a `ℚ`-algebra map: it fixes the image of `ℚ`.
example (q : ℚ) :
    equivAlgebraicClosureRat (algebraMap ℚ (AlgebraicClosure ℚ) q) = algebraMap ℚ Qbar q :=
  AlgEquiv.commutes equivAlgebraicClosureRat q

-- Countability is now available to instance search anywhere `AlgebraicClosure ℚ` appears.
example : Countable (AlgebraicClosure ℚ) := inferInstance

-- And the concrete algebraic numbers are countable as a type.
example : Countable Qbar := inferInstance

end Examples

end AlgebraicNumbersCountableOQ01OQ03
