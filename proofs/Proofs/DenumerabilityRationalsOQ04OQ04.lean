/-
# Promoting Countability of the Algebraic Numbers to Denumerability

Open question (denumerability family, `denumerability-rationals-oq-04-oq-04`),
building on `denumerability-rationals-oq-04` (the algebraic numbers over ℚ are
countable):

  "Can this proof be promoted from `Countable` to `Denumerable` — an explicit
   bijection `Q̄ ≅ ℕ` — without sacrificing constructiveness? The challenge is
   computing the index of a given algebraic number in the enumeration."

## What is proved

Let `AlgQ := {x : ℂ // IsAlgebraic ℚ x}` be the field of complex algebraic
numbers. We give it a `Denumerable` structure — the strongest countability
notion in Mathlib, an *explicit bijection with ℕ* — obtained by combining:

* **Countability** `Algebraic.countable ℚ ℂ` (already in Mathlib: the algebraic
  elements of a `Countable` base ring are countable), and
* **Infinitude** `Infinite AlgQ` (ℚ embeds into `AlgQ` via `algebraMap ℚ ℂ`),

through `Denumerable.ofEncodableOfInfinite`. This yields
`algebraicEquivNat : AlgQ ≃ ℕ`, the requested bijection `Q̄ ≅ ℕ`, together with
the cardinality statement `#AlgQ = ℵ₀`.

## The constructive caveat (the open part of the question)

The `Denumerable` instance here is **classical / noncomputable**: it factors
through `Encodable.ofCountable`, which uses `Classical.choice` to extract an
encoding from a mere countability proof. So the bijection exists but does not
*compute* — it does not give an algorithm mapping an algebraic number to its
index. A genuinely *constructive* enumeration (the "without sacrificing
constructiveness" of the question) would require effective root isolation
(Sturm sequences / Vincent's theorem) to list the roots of each integer
polynomial in a computable order; that remains open (it is open question 1 of
the parent). The honest status: denumerability holds, an explicit `≃ ℕ` exists,
but computing the index is the unresolved constructive challenge.

`Classical.choice`, `propext`, and `Quot.sound` are the only axioms used — the
standard foundational trio, none of which is `Lean.ofReduceBool` or `sorryAx`.
So this file is verified (0 sorries, 0 `axiom` declarations); it is merely
`noncomputable`.

Axioms: 0 (Classical.choice / propext / Quot.sound only — the foundational trio)
Sorries: 0
-/

import Mathlib

open Cardinal

namespace DenumerabilityRationalsOQ04OQ04

/-- The complex algebraic numbers over ℚ. -/
abbrev AlgQ : Type := {x : ℂ // IsAlgebraic ℚ x}

/-- The algebraic numbers are countable — Mathlib's `Algebraic.countable`
specialised to `ℚ ⊆ ℂ` (ℚ is a countable base ring). -/
instance : Countable AlgQ :=
  (Algebraic.countable ℚ ℂ).to_subtype

/-- ℚ embeds into the algebraic numbers via `algebraMap ℚ ℂ` (every rational is
algebraic), so there are infinitely many algebraic numbers. -/
instance : Infinite AlgQ :=
  Infinite.of_injective
    (fun q : ℚ => (⟨algebraMap ℚ ℂ q, isAlgebraic_algebraMap q⟩ : AlgQ))
    (fun a b h =>
      FaithfulSMul.algebraMap_injective ℚ ℂ (Subtype.ext_iff.1 h))

/-- **The Denumerable instance.** Countable + Infinite gives an explicit
bijection with ℕ. Classical/noncomputable: the encoding is extracted from the
countability proof via `Classical.choice`. -/
noncomputable instance instDenumerableAlgQ : Denumerable AlgQ :=
  haveI : Encodable AlgQ := Encodable.ofCountable AlgQ
  Denumerable.ofEncodableOfInfinite AlgQ

/-- **The explicit bijection `Q̄ ≅ ℕ`** requested by the open question. -/
noncomputable def algebraicEquivNat : AlgQ ≃ ℕ :=
  Denumerable.eqv AlgQ

/-- A `Denumerable` structure on the algebraic numbers exists (the choiceless
existence statement, independent of the chosen instance). -/
theorem nonempty_denumerable_algQ : Nonempty (Denumerable AlgQ) :=
  nonempty_denumerable AlgQ

/-- An explicit bijection between the algebraic numbers and ℕ exists. -/
theorem nonempty_equiv_nat : Nonempty (AlgQ ≃ ℕ) :=
  ⟨algebraicEquivNat⟩

/-- The algebraic numbers have cardinality `ℵ₀` — the cardinal-arithmetic form
of denumerability (Mathlib's `cardinalMk_of_countable_of_charZero`). -/
theorem cardinalMk_algQ : #AlgQ = ℵ₀ :=
  Algebraic.cardinalMk_of_countable_of_charZero ℚ ℂ

/-- Denumerability is equivalent to `#AlgQ = ℵ₀`: the bijection with ℕ and the
cardinal statement carry the same information. -/
theorem denumerable_iff_cardinal : Nonempty (Denumerable AlgQ) ↔ #AlgQ = ℵ₀ := by
  constructor
  · intro _; exact cardinalMk_algQ
  · intro _; exact nonempty_denumerable_algQ

end DenumerabilityRationalsOQ04OQ04
