/-
# Quantitative Cantor: the strict cardinality gap `#A < #(A → Prop)`
## (cantor-diagonalization-oq-03-oq-01-incomplete-01-oq-01-oq-03)

**Open question #3** from the parent entry
`cantor-diagonalization-oq-03-oq-01-incomplete-01-oq-01`
("Reflexive Objects and the Fixed-Point Property"):

> **Quantitative Cantor**: extend `cantor_surjective_recovered` to a cardinality gap statement
> `|A| < |A → Prop|` rather than mere non-surjectivity.

## What the parent proved, and what this adds

The parent obtained the *qualitative* Cantor obstruction as an instance of the Lawvere
fixed-point argument: no `e : A → (A → Prop)` is surjective (`cantor_surjective_recovered`),
because `Not : Prop → Prop` has no fixed point. That is a statement about *maps*.

This entry records the *quantitative* strengthening, a statement about *cardinals*: the two
cardinals `#A` and `#(A → Prop)` are not merely distinct, they are strictly ordered,

  `#A < #(A → Prop)`   for every type `A`.

Because a surjection `A ↠ B` forces `#B ≤ #A` (`Cardinal.mk_le_of_surjective`), the strict gap
*re-implies* the parent's non-surjectivity (`not_surjective_of_cardinality_gap`). So the gap is
genuinely stronger: it recovers the qualitative result and additionally pins down the *direction*
and *strictness* of the size difference.

## The proof

`A → Prop` is definitionally `Set A`, so the gap is exactly Mathlib's
`Cardinal.cantor` (`a < 2 ^ a`) transported along `Cardinal.mk_set` (`#(Set A) = 2 ^ #A`).
No new mathematics is required beyond identifying the predicate type with the power set — the
content is that the open question is a one-line consequence of the standard cardinal Cantor
theorem, which the parent's bespoke Lawvere development did not phrase at the cardinal level.

## Status

**Sorry count**: 0. **Axiom count**: 0 literal `axiom` declarations; the results use only the
foundational `propext` / `Classical.choice` / `Quot.sound`. Gallery status: `verified`.
-/

import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Tactic

open Function
open scoped Cardinal

namespace CantorDiagonalizationOQ03OQ01Incomplete01OQ01OQ03

universe u

/-- **Quantitative Cantor (power-set form).** For every type `A`, the power set `Set A` is
strictly larger than `A`: `#A < #(Set A) = 2 ^ #A`. This is `Cardinal.cantor` phrased on the type
of subsets. -/
theorem cardinality_gap_set (A : Type u) : #A < #(Set A) := by
  rw [Cardinal.mk_set]
  exact Cardinal.cantor _

/-- **Quantitative Cantor (predicate form).** The strict cardinality gap between a type and its
type of predicates: `#A < #(A → Prop)`. This is the exact strengthening of the parent's
`cantor_surjective_recovered` (mere non-surjectivity of every `A → (A → Prop)`) requested in the
open question. `A → Prop` is definitionally `Set A`, so it is `cardinality_gap_set`. -/
theorem cardinality_gap (A : Type u) : #A < #(A → Prop) :=
  cardinality_gap_set A

/-- **The gap re-implies the parent's qualitative Cantor.** No map `e : A → (A → Prop)` is
surjective: a surjection `A ↠ (A → Prop)` would force `#(A → Prop) ≤ #A`
(`Cardinal.mk_le_of_surjective`), contradicting the strict gap `#A < #(A → Prop)`. Hence
`cardinality_gap` is strictly stronger than `cantor_surjective_recovered`. -/
theorem not_surjective_of_cardinality_gap {A : Type u} (e : A → (A → Prop)) :
    ¬ Surjective e := by
  intro hsurj
  have hle : #(A → Prop) ≤ #A := Cardinal.mk_le_of_surjective hsurj
  exact absurd hle (not_le_of_gt (cardinality_gap A))

/-- Sanity check: the predicate-form gap is literally the power-set-form gap, since `Set A` and
`A → Prop` are definitionally equal. -/
example (A : Type u) : (#A < #(A → Prop)) = (#A < #(Set A)) := rfl

#check @cardinality_gap_set
#check @cardinality_gap
#check @not_surjective_of_cardinality_gap

end CantorDiagonalizationOQ03OQ01Incomplete01OQ01OQ03
