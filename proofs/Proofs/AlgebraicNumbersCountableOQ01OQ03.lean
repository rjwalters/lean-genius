/-
  # The Algebraic Numbers ARE an Algebraic Closure of ℚ

  ## Lineage

  * Grandparent (`AlgebraicNumbersCountable`): the algebraic numbers form a
    *countable* subset of ℂ; in fact `#{z : ℂ | IsAlgebraic ℚ z} = ℵ₀`.
  * Parent (`AlgebraicNumbersCountableOQ01`): the algebraic elements of a field
    extension `L / K` are closed under `+, -, *, ⁻¹`, hence form a *subfield*.
  * Sibling (`AlgebraicNumbersCountableOQ01OQ01`): that subfield is upgraded to an
    `IntermediateField` `algebraicNumbersField : IntermediateField ℚ ℂ`, shown to be
    *algebraically closed*, and identified with Mathlib's *relative* algebraic
    closure `algebraicClosure ℚ ℂ`.

  ## What this file adds (open question `oq-01-oq-03`)

  The sibling identifies the algebraic numbers with the *relative* closure
  `algebraicClosure ℚ ℂ` — an object that still lives inside `ℂ`. The open question
  asks for the last structural step: identify the algebraic numbers with the
  *abstract* algebraic closure `AlgebraicClosure ℚ`, the closure built by Mathlib
  from `ℚ` alone with no ambient field.

  The bridge is the universal "any two algebraic closures are isomorphic" principle.
  Concretely:

  1. **`algebraicNumbersField` is an algebraic closure of `ℚ`.** It is algebraically
     closed (sibling) *and* algebraic over `ℚ` (every element is algebraic, by
     definition), the two halves of Mathlib's `IsAlgClosure ℚ ·` predicate
     (`instance : IsAlgClosure ℚ algebraicNumbersField`).

  2. **The isomorphism.** Since `AlgebraicClosure ℚ` is also an `IsAlgClosure ℚ ·`,
     Mathlib's `IsAlgClosure.equiv` yields a `ℚ`-algebra isomorphism
     `algebraicNumbersEquivAlgebraicClosure : algebraicNumbersField ≃ₐ[ℚ] AlgebraicClosure ℚ`.
     As a `ℚ`-algebra map it automatically fixes `ℚ` pointwise.

  3. **Cardinality transport.** A `ℚ`-algebra isomorphism is in particular a
     bijection, so the grandparent's count `#(algebraic numbers) = ℵ₀` transfers to
     the abstract closure:
     `#(AlgebraicClosure ℚ) = ℵ₀`  (`cardinalMk_algebraicClosure_rat`),
     and hence `AlgebraicClosure ℚ` is a `Countable` type
     (`countable_algebraicClosure_rat`). This realizes the classical fact that
     "the field of algebraic numbers is countable" for the *intrinsically* defined
     algebraic closure, not merely for its concrete copy inside `ℂ`.

  All results are fully verified: 0 sorries, 0 `axiom` declarations, 0
  structure-encoded assumptions (only the foundational `propext`,
  `Classical.choice`, `Quot.sound`).

  The mathematical content here is the *transport*: the sibling supplies the
  algebraically-closed intermediate field, Mathlib supplies the uniqueness of
  algebraic closures, and combining them pins the abstract `AlgebraicClosure ℚ`
  down to the concrete algebraic numbers — including the transfer of countability.

  Tags: field-theory, algebraic-numbers, algebraic-closure, cardinality, countable
-/
import Mathlib
import Proofs.AlgebraicNumbersCountableOQ01OQ01

open Cardinal

namespace AlgebraicNumbersCountableOQ01OQ03

open AlgebraicNumbersCountableOQ01OQ01

/- ============================================================
   § 1 : The algebraic numbers are an algebraic closure of ℚ
   ============================================================ -/

/-- **The algebraic numbers form an algebraic closure of `ℚ`.**

`IsAlgClosure ℚ K` packages the two defining properties of an algebraic closure:
`K` is algebraically closed and `K / ℚ` is an algebraic extension. The sibling file
supplies the first (`IsAlgClosed algebraicNumbersField`) and the parent's
construction supplies the second (every algebraic number is, by definition,
algebraic over `ℚ`). -/
instance instIsAlgClosure : IsAlgClosure ℚ algebraicNumbersField where
  isAlgClosed := inferInstance
  isAlgebraic := inferInstance

/- ============================================================
   § 2 : Identification with the abstract `AlgebraicClosure ℚ`
   ============================================================ -/

/-- **Main theorem (open question `oq-01-oq-03`).** The concrete field of algebraic
numbers inside `ℂ` is `ℚ`-algebra isomorphic to Mathlib's abstractly-constructed
`AlgebraicClosure ℚ`.

Both are algebraic closures of `ℚ` (`instIsAlgClosure` and Mathlib's instance for
`AlgebraicClosure ℚ`), and any two algebraic closures of the same field are
isomorphic over it — Mathlib's `IsAlgClosure.equiv`. The isomorphism is a
`ℚ`-algebra equivalence, so it is simultaneously a field isomorphism and fixes
`ℚ` pointwise. -/
noncomputable def algebraicNumbersEquivAlgebraicClosure :
    algebraicNumbersField ≃ₐ[ℚ] AlgebraicClosure ℚ :=
  IsAlgClosure.equiv ℚ algebraicNumbersField (AlgebraicClosure ℚ)

/-- The identification is a `ℚ`-algebra map, hence fixes every rational: it sends
`algebraMap ℚ algebraicNumbersField q` to `algebraMap ℚ (AlgebraicClosure ℚ) q`. -/
@[simp] theorem algebraicNumbersEquivAlgebraicClosure_commutes (q : ℚ) :
    algebraicNumbersEquivAlgebraicClosure (algebraMap ℚ algebraicNumbersField q)
      = algebraMap ℚ (AlgebraicClosure ℚ) q :=
  algebraicNumbersEquivAlgebraicClosure.commutes q

/- ============================================================
   § 3 : Cardinality transport — `AlgebraicClosure ℚ` is countable
   ============================================================ -/

/-- The underlying type of the algebraic-numbers field has cardinality `ℵ₀`.

The carrier of `algebraicNumbersField` is the subtype `{z : ℂ // IsAlgebraic ℚ z}`,
whose cardinality is `ℵ₀` by Mathlib's
`Algebraic.cardinalMk_of_countable_of_charZero` (`ℚ` is countable of characteristic
zero). -/
theorem cardinalMk_algebraicNumbersField :
    #(algebraicNumbersField) = ℵ₀ :=
  -- the carrier `↥algebraicNumbersField` is *definitionally* `{z : ℂ // IsAlgebraic ℚ z}`,
  -- since membership unfolds to `IsAlgebraic ℚ ·` (`mem_algebraicIntermediateField`).
  Algebraic.cardinalMk_of_countable_of_charZero ℚ ℂ

/-- **The abstract algebraic closure of `ℚ` is countably infinite:**
`#(AlgebraicClosure ℚ) = ℵ₀`.

This transports the grandparent's count of the algebraic numbers across the
isomorphism `algebraicNumbersEquivAlgebraicClosure`. While "the algebraic numbers
are countable" is classical, here it is established for the *intrinsic*
`AlgebraicClosure ℚ`, which carries no a-priori embedding into `ℂ`. -/
theorem cardinalMk_algebraicClosure_rat :
    #(AlgebraicClosure ℚ) = ℵ₀ :=
  (Cardinal.mk_congr algebraicNumbersEquivAlgebraicClosure.toEquiv).symm.trans
    cardinalMk_algebraicNumbersField

/-- The abstract algebraic closure `AlgebraicClosure ℚ` is a `Countable` type. -/
theorem countable_algebraicClosure_rat : Countable (AlgebraicClosure ℚ) :=
  Cardinal.mk_le_aleph0_iff.mp (le_of_eq cardinalMk_algebraicClosure_rat)

/-- `AlgebraicClosure ℚ` is, moreover, infinite, so the count `ℵ₀` is genuine
countable infinity rather than mere countability. -/
theorem infinite_algebraicClosure_rat : Infinite (AlgebraicClosure ℚ) :=
  Cardinal.infinite_iff.mpr (le_of_eq cardinalMk_algebraicClosure_rat.symm)

section Examples

-- The isomorphism is a bijection between the two carriers.
example : Function.Bijective algebraicNumbersEquivAlgebraicClosure :=
  algebraicNumbersEquivAlgebraicClosure.bijective

-- `AlgebraicClosure ℚ` is countable and infinite — i.e. countably infinite.
example : Countable (AlgebraicClosure ℚ) := countable_algebraicClosure_rat
example : Infinite (AlgebraicClosure ℚ) := infinite_algebraicClosure_rat

end Examples

end AlgebraicNumbersCountableOQ01OQ03
