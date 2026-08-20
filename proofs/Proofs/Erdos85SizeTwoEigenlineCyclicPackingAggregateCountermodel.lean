import Mathlib

/-!
# Aggregate countermodel for the cyclic packing moment route

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

The selected-orbit moment and marginal identities alone cannot prove the
packing exclusion.  This file records the obstruction as an exact abstract
incidence model: every difference fiber uses every allowed absolute cell
once.  It has zero within-fiber collisions, uniform full multiplicity, and
attains sharp-support Cauchy with equality.  All collision pressure is
absorbed by distinct fiber pairs.  A successful packing proof must therefore
use displacement-resolved reciprocity, not only aggregate moments.
-/

namespace Erdos85

noncomputable section

/-- The aggregate uniform model has one incidence from every selected fiber
to every allowed absolute cell. -/
def sizeTwoCyclicUniformAggregateMultiplicity
    {T E : Type*} (t : T) (e : E) : ℕ := 1

/-- Every fiber of the uniform aggregate model has mass equal to the allowed
support size. -/
theorem sizeTwoCyclicUniformAggregateMultiplicity_fiber_sum
    {T E : Type*} [Fintype E] (t : T) :
    (∑ e : E, sizeTwoCyclicUniformAggregateMultiplicity t e) =
      Fintype.card E := by
  simp [sizeTwoCyclicUniformAggregateMultiplicity]

/-- Each absolute cell has total multiplicity equal to the number of selected
difference fibers. -/
theorem sizeTwoCyclicUniformAggregateMultiplicity_cell_sum
    {T E : Type*} [Fintype T] (e : E) :
    (∑ t : T, sizeTwoCyclicUniformAggregateMultiplicity t e) =
      Fintype.card T := by
  simp [sizeTwoCyclicUniformAggregateMultiplicity]

/-- The model is stronger than the same-difference agreement cap at the
aggregate level: a single fiber has no repeated target cell at all. -/
theorem sizeTwoCyclicUniformAggregateMultiplicity_within_collision_zero
    {T E : Type*} [Fintype E] (t : T) :
    (∑ e : E,
      (sizeTwoCyclicUniformAggregateMultiplicity t e).choose 2) = 0 := by
  simp [sizeTwoCyclicUniformAggregateMultiplicity]

/-- The combined multiplicity square-mass is exactly support size times the
square of the number of selected fibers. -/
theorem sizeTwoCyclicUniformAggregateMultiplicity_square_sum
    {T E : Type*} [Fintype T] [Fintype E] :
    (∑ e : E, (∑ t : T,
      sizeTwoCyclicUniformAggregateMultiplicity t e) ^ 2) =
      Fintype.card E * Fintype.card T ^ 2 := by
  simp [sizeTwoCyclicUniformAggregateMultiplicity]

/-- Consequently sharp-support Cauchy is an equality in the aggregate model.
This is the formal obstruction to closing the packing gap using the currently
banked moment/marginal inequalities alone. -/
theorem sizeTwoCyclicUniformAggregateMultiplicity_cauchy_equality
    {T E : Type*} [Fintype T] [Fintype E] :
    (Fintype.card T * Fintype.card E) ^ 2 =
      Fintype.card E * ∑ e : E, (∑ t : T,
        sizeTwoCyclicUniformAggregateMultiplicity t e) ^ 2 := by
  rw [sizeTwoCyclicUniformAggregateMultiplicity_square_sum]
  ring

/-- In the binary packing parameters, `q-2` fibers on `q(q-2)` allowed
cells realize all exact aggregate masses and saturate Cauchy. -/
theorem binarySizeTwoCyclic_uniformAggregate_parameters
    (q : ℕ) :
    let T := Fin (q - 2)
    let E := Fin (q * (q - 2))
    (∀ t : T, (∑ e : E,
        sizeTwoCyclicUniformAggregateMultiplicity t e) = q * (q - 2)) ∧
    (∀ e : E, (∑ t : T,
        sizeTwoCyclicUniformAggregateMultiplicity t e) = q - 2) ∧
    (∀ t : T, (∑ e : E,
        (sizeTwoCyclicUniformAggregateMultiplicity t e).choose 2) = 0) ∧
    (((q - 2) * (q * (q - 2))) ^ 2 =
      (q * (q - 2)) * ∑ e : E, (∑ t : T,
        sizeTwoCyclicUniformAggregateMultiplicity t e) ^ 2) := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t
    simpa using
      (sizeTwoCyclicUniformAggregateMultiplicity_fiber_sum
        (T := Fin (q - 2)) (E := Fin (q * (q - 2))) t)
  · intro e
    simpa using
      (sizeTwoCyclicUniformAggregateMultiplicity_cell_sum
        (T := Fin (q - 2)) (E := Fin (q * (q - 2))) e)
  · intro t
    exact sizeTwoCyclicUniformAggregateMultiplicity_within_collision_zero
      (E := Fin (q * (q - 2))) t
  · simpa using
      (sizeTwoCyclicUniformAggregateMultiplicity_cauchy_equality
        (T := Fin (q - 2)) (E := Fin (q * (q - 2))))

end

end Erdos85

#print axioms
  Erdos85.sizeTwoCyclicUniformAggregateMultiplicity_cauchy_equality
#print axioms Erdos85.binarySizeTwoCyclic_uniformAggregate_parameters
