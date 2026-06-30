/-
  # The Algebraic Numbers Form an Algebraically Closed Field

  The parent file (`AlgebraicNumbersCountableOQ01`) proves that the elements of a
  field extension `L / K` that are algebraic over `K` are closed under `+, -, *, ⁻¹`
  and hence form a *subfield* `algebraicSubfield K L : Subfield L`. For `K = ℚ`,
  `L = ℂ` this is the field of algebraic numbers, which the grandparent proof
  (`AlgebraicNumbersCountable`) shows is *countable*.

  This file pushes that one decisive step further: the field of algebraic numbers is
  not merely a subfield, it is an **algebraically closed** field — the relative
  algebraic closure of `K` in `L` whenever `L` itself is algebraically closed.

  ## What is proved

  1. **Upgrade to an intermediate field.** `algebraicSubfield K L` is promoted to an
     `IntermediateField K L` (`algebraicIntermediateField K L`); the only extra datum
     is that `K` itself lands inside it, because `algebraMap K L k` is algebraic over
     `K` (`isAlgebraic_algebraMap`).

  2. **Agreement with Mathlib.** This intermediate field is exactly Mathlib's relative
     algebraic closure `algebraicClosure K L`
     (`algebraicIntermediateField_eq_algebraicClosure`), so the parent's hand-built
     `algebraicSubfield` recovers the standard object.

  3. **Closed under taking algebraic elements (transitivity).** If `z : L` is algebraic
     over the field of algebraic elements, then `z` is already algebraic over `K`,
     hence already in the field (`mem_of_isAlgebraic_over`). This is the crux: it is
     *transitivity of algebraicity* (`IsIntegral.trans_isAlgebraic`) — an algebraic
     element of an algebraic extension is algebraic over the base.

  4. **Algebraic closedness.** When `L` is algebraically closed, the field of algebraic
     elements is itself algebraically closed
     (`isAlgClosed_algebraicIntermediateField`): any nonconstant polynomial over it has
     a root in `L` (since `L` is closed), that root is algebraic over the field, hence
     by (3) it already lives *in* the field. The proof is a direct, self-contained
     transitivity argument via `IsAlgClosed.of_exists_root`, not an appeal to Mathlib's
     packaged `IsAlgClosure` instance.

  5. **Specialization to ℚ ⊆ ℂ.** The algebraic numbers `algebraicNumbersField : IntermediateField ℚ ℂ`
     form an algebraically closed field — an algebraic closure of ℚ realized concretely
     inside ℂ — while remaining countable (parent result). So ℂ is a strictly larger,
     uncountable algebraically closed field containing it.

  Tags: field-theory, algebraic-numbers, algebraic-closure, intermediate-field,
        transitivity-of-algebraicity, integral-closure
-/
import Proofs.AlgebraicNumbersCountableOQ01
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic

open AlgebraicNumbersCountableOQ01

namespace AlgebraicNumbersCountableOQ01OQ01

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/- ============================================================
   § 1 : Upgrade the parent's subfield to an intermediate field
   ============================================================ -/

/-- The elements of `L` algebraic over `K`, packaged as an **intermediate field**
    `K ⊆ · ⊆ L`. This upgrades the parent's `algebraicSubfield K L : Subfield L`; the
    extra requirement for an intermediate field is that the image of `K` is contained,
    which holds because each `algebraMap K L k` is algebraic over `K`. -/
def algebraicIntermediateField : IntermediateField K L :=
  (algebraicSubfield K L).toIntermediateField fun k =>
    mem_algebraicSubfield.mpr (isAlgebraic_algebraMap k)

variable {K L}

@[simp] theorem mem_algebraicIntermediateField {x : L} :
    x ∈ algebraicIntermediateField K L ↔ IsAlgebraic K x := Iff.rfl

/-- The parent's hand-built field of algebraic elements is exactly Mathlib's relative
    algebraic closure `algebraicClosure K L`. -/
theorem algebraicIntermediateField_eq_algebraicClosure :
    algebraicIntermediateField K L = algebraicClosure K L := by
  ext x
  rw [mem_algebraicIntermediateField, mem_algebraicClosure_iff]

/-- The field of algebraic elements is, as an extension of `K`, an algebraic extension:
    every one of its elements is algebraic over `K`. -/
instance algebraicIntermediateField_isAlgebraic :
    Algebra.IsAlgebraic K (algebraicIntermediateField K L) :=
  ⟨fun x => IntermediateField.isAlgebraic_iff.mpr
    (mem_algebraicIntermediateField.mp x.2)⟩

/- ============================================================
   § 2 : Closed under taking algebraic elements (transitivity)
   ============================================================ -/

/-- **Transitivity heart.** If `z : L` is algebraic over the field of algebraic
    elements `A = algebraicIntermediateField K L`, then `z` is already algebraic over
    the base field `K`, hence already a member of `A`.

    Mathematically: `A / K` is algebraic, so an algebraic element of `L` over `A` is
    algebraic over `K` (`IsIntegral.trans_isAlgebraic`). This is precisely the closure
    property that makes `A` the *algebraic* closure rather than a mere subfield. -/
theorem mem_of_isAlgebraic_over {z : L}
    (hz : IsAlgebraic (algebraicIntermediateField K L) z) :
    z ∈ algebraicIntermediateField K L := by
  rw [mem_algebraicIntermediateField]
  -- `z` is integral over `A` (field base), and `A / K` is algebraic, so `z` alg./K
  exact hz.isIntegral.trans_isAlgebraic (R := K)

/- ============================================================
   § 3 : The field of algebraic elements is algebraically closed
   ============================================================ -/

/-- **Main theorem.** If `L` is algebraically closed, then the field of elements of `L`
    algebraic over `K` is itself algebraically closed.

    Proof (self-contained, via transitivity): let `p` be a monic irreducible polynomial
    over `A = algebraicIntermediateField K L`. Viewing its coefficients in `L`, the fact
    that `L` is algebraically closed yields a root `w ∈ L`. That `w` is integral over
    `A` (it is a root of the *monic* `p`), and `A / K` is algebraic, so by transitivity
    `w` is algebraic over `K` — i.e. `w ∈ A`. The root therefore already lives in `A`,
    so every nonconstant polynomial over `A` has a root in `A`. -/
theorem isAlgClosed_algebraicIntermediateField [IsAlgClosed L] :
    IsAlgClosed (algebraicIntermediateField K L) := by
  apply IsAlgClosed.of_exists_root
  intro p hmon hirr
  -- `p` has positive degree
  have hdeg : p.degree ≠ 0 := (Polynomial.degree_pos_of_irreducible hirr).ne'
  -- `L` is algebraically closed ⇒ `p` (coeffs in `L`) has a root `w : L`
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_aeval_eq_zero L p hdeg
  -- `w` is integral over `A`: it is a root of the monic polynomial `p`
  have hwint : IsIntegral (algebraicIntermediateField K L) w := ⟨p, hmon, hw⟩
  -- transitivity: algebraic over the (algebraic over `K`) field ⇒ algebraic over `K`
  have hwmem : w ∈ algebraicIntermediateField K L :=
    mem_of_isAlgebraic_over hwint.isAlgebraic
  -- so the root `⟨w, hwmem⟩` lives in `A`; transport `aeval w p = 0` along the
  -- injective inclusion `A ↪ L`
  refine ⟨⟨w, hwmem⟩, ?_⟩
  have hbridge :
      algebraMap (algebraicIntermediateField K L) L (p.eval ⟨w, hwmem⟩) = 0 := by
    rw [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
    simpa using hw
  exact (FaithfulSMul.algebraMap_injective (algebraicIntermediateField K L) L)
    (by simpa using hbridge)

/- ============================================================
   § 4 : Specialization — the algebraic numbers ℚ̄ ⊆ ℂ
   ============================================================ -/

/-- The **algebraic numbers**, realized concretely as the intermediate field of all
    complex numbers algebraic over `ℚ`. The grandparent proof shows this field is
    *countable*; the theorem below shows it is *algebraically closed*. -/
noncomputable abbrev algebraicNumbersField : IntermediateField ℚ ℂ :=
  algebraicIntermediateField ℚ ℂ

/-- The field of algebraic numbers is algebraically closed: it is an algebraic closure
    of `ℚ` sitting inside `ℂ`. -/
instance : IsAlgClosed algebraicNumbersField :=
  isAlgClosed_algebraicIntermediateField

/-- The field of algebraic numbers coincides with Mathlib's relative algebraic closure
    `algebraicClosure ℚ ℂ`. -/
theorem algebraicNumbersField_eq : algebraicNumbersField = algebraicClosure ℚ ℂ :=
  algebraicIntermediateField_eq_algebraicClosure

section Examples

-- A complex number is an algebraic number iff it is algebraic over `ℚ`.
example {z : ℂ} : z ∈ algebraicNumbersField ↔ IsAlgebraic ℚ z :=
  mem_algebraicIntermediateField

-- Membership is closed under the algebraic-closure step: an algebraic combination of
-- algebraic numbers that solves a polynomial over the algebraic numbers is algebraic.
example {z : ℂ} (hz : IsAlgebraic algebraicNumbersField z) : z ∈ algebraicNumbersField :=
  mem_of_isAlgebraic_over hz

end Examples

end AlgebraicNumbersCountableOQ01OQ01
