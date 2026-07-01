import Mathlib

/-
# Countability of the Algebraic Elements is Governed by the Base Field

## Open Question OQ-05-OQ-04

The parent entry `AlgebraicNumbersCountableOQ05` proves, via Cantor's 1874 height
function, that the real algebraic numbers `{x : ℝ | IsAlgebraic ℚ x}` are countable.  The
open question asks whether this generalizes to algebraic numbers over *other* base fields:

> Does the proof generalize to algebraic numbers over other fields — for example algebraic
> numbers over `ℚ(√2)`, or algebraic `p`-adic numbers?

## The subtlety, and the sharp answer

The naive reading — "algebraic elements over any field are countable" — is **false**, and
the phrase "algebraic `p`-adic numbers" is exactly where it breaks: the `p`-adic field
`ℚ_p` is *uncountable*, and every one of its (uncountably many) elements is trivially
algebraic over `ℚ_p`.  So the algebraic elements over `ℚ_p` are uncountable.

What is actually true is a **sharp characterization**: for a field extension `L / K`,

  `{x : L | IsAlgebraic K x}` is countable  ↔  the base field `K` is countable.

The countability of the *ambient* field `L` is irrelevant; only the *base* field's
cardinality matters.  This both confirms the parent's result (`ℚ` is countable) and
explains precisely why the `p`-adic generalization fails (`ℚ_p` is not).

## Contribution

* `algebraic_setOf_countable`  — the **sufficient** direction (the parent's "yes"):
  a countable base field has a countable set of algebraic elements in any extension.
  This is Mathlib's `Algebraic.countable`, restated for field extensions.
* `algebraMap_mem_algebraic`  — every element of the base field is algebraic over it, so
  `K` embeds into the algebraic set through the injective `algebraMap`.
* `countable_of_algebraic_setOf_countable`  — the **necessary** direction: if the algebraic
  set is countable then the base field is countable (pull back the embedding).
* `countable_algebraic_iff`  — the two directions assembled into the sharp
  characterization `Countable {x | IsAlgebraic K x} ↔ Countable K`.
* `not_countable_algebraic_of_uncountable_base`  — the contrapositive: an uncountable base
  field forces uncountably many algebraic elements.  This is the general form of the
  `p`-adic obstruction.
* Worked instances: algebraic elements over `ℚ` and over a finite field `ZMod p` are
  countable; algebraic elements over `ℝ` (inside `ℂ`) are **un**countable — the cautionary
  example standing in for the `p`-adic case, needing no `p`-adic machinery.

## Axioms: 0 | Sorries: 0
-/

namespace AlgebraicNumbersCountableOQ05OQ04

open Set

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-! ### Sufficient direction: countable base ⟹ countable algebraic set -/

/-- **Sufficient direction (the parent's "yes").**  When the base field `K` is countable,
    the set of elements of any field extension `L` that are algebraic over `K` is countable.
    This is Mathlib's `Algebraic.countable` specialized to fields; the ambient field `L`
    plays no role in the hypothesis. -/
theorem algebraic_setOf_countable [Countable K] :
    Set.Countable {x : L | IsAlgebraic K x} :=
  Algebraic.countable K L

/-! ### The base field embeds into the algebraic set -/

/-- Every element of the base field is algebraic over it: `algebraMap K L k` is a root of the
    linear polynomial `X - k`.  Hence the base field lands inside the algebraic set. -/
theorem algebraMap_mem_algebraic (k : K) :
    algebraMap K L k ∈ {x : L | IsAlgebraic K x} :=
  isAlgebraic_algebraMap k

/-! ### Necessary direction: countable algebraic set ⟹ countable base -/

/-- **Necessary direction.**  If the set of elements algebraic over `K` is countable, then
    the base field `K` itself is countable.  The map `k ↦ algebraMap K L k` is an injection
    of `K` into the (now countable) algebraic set — `algebraMap` is injective because `K` is
    a field and `L` is nontrivial — so `K` inherits countability. -/
theorem countable_of_algebraic_setOf_countable
    (h : Set.Countable {x : L | IsAlgebraic K x}) : Countable K := by
  haveI : Countable {x : L | IsAlgebraic K x} := h.to_subtype
  have hf : Function.Injective
      (fun k : K => (⟨algebraMap K L k, isAlgebraic_algebraMap k⟩ :
        {x : L | IsAlgebraic K x})) := by
    intro a b hab
    have hval : algebraMap K L a = algebraMap K L b := congrArg Subtype.val hab
    exact FaithfulSMul.algebraMap_injective K L hval
  exact hf.countable

/-! ### The sharp characterization -/

/-- **The sharp characterization.**  For a field extension `L / K`, the set of elements of
    `L` algebraic over `K` is countable **iff** the base field `K` is countable.  Only the
    base field's cardinality matters — the size of the ambient field `L` is irrelevant. -/
theorem countable_algebraic_iff :
    Set.Countable {x : L | IsAlgebraic K x} ↔ Countable K :=
  ⟨countable_of_algebraic_setOf_countable, fun h => by
    haveI := h
    exact algebraic_setOf_countable⟩

/-- **The `p`-adic obstruction, in general form.**  If the base field `K` is uncountable
    then the algebraic elements over `K` are uncountable — indeed `K` alone already supplies
    uncountably many of them.  This is why "algebraic `p`-adic numbers" are not countable:
    `ℚ_p` is uncountable. -/
theorem not_countable_algebraic_of_uncountable_base (h : ¬ Countable K) :
    ¬ Set.Countable {x : L | IsAlgebraic K x} :=
  fun hc => h (countable_of_algebraic_setOf_countable hc)

/-! ### Worked instances

Concrete base fields on both sides of the characterization. -/

section Examples

/-- Algebraic elements over `ℚ` (in any field extension) are countable — the classical case,
    now recovered as a one-line instance of the general theorem rather than through Cantor's
    height function. -/
example {L : Type*} [Field L] [Algebra ℚ L] :
    Set.Countable {x : L | IsAlgebraic ℚ x} :=
  algebraic_setOf_countable

/-- Algebraic elements over a finite field `ZMod p` are countable: `ZMod p` is finite, hence
    countable, so the characterization applies.  (This is the function-field analogue of the
    number-field case.) -/
example (p : ℕ) [Fact p.Prime] {L : Type*} [Field L] [Algebra (ZMod p) L] :
    Set.Countable {x : L | IsAlgebraic (ZMod p) x} :=
  algebraic_setOf_countable

/-- **The cautionary example** standing in for the `p`-adic case.  The base field `ℝ` is
    uncountable, so the elements of `ℂ` algebraic over `ℝ` are uncountable — even though
    `ℂ` is algebraic over `ℝ` of degree `2`.  No `p`-adic machinery is needed to see the
    obstruction: uncountability of the base is enough. -/
example : ¬ Set.Countable {x : ℂ | IsAlgebraic ℝ x} :=
  not_countable_algebraic_of_uncountable_base not_countable

end Examples

end AlgebraicNumbersCountableOQ05OQ04
