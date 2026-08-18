import Proofs.Erdos85MuThreeSixPointDerangementTypeCocycle

/-!
# Commutator types distinguish six-point derangement cocycle patterns

After conjugating one factor to a canonical representative, the remaining
finite calculation is only one-dimensional.  It shows that the commutator
has sharply different cycle type in the all-`(4,2)`, exactly-one-`(3,3)`, and
all-`(3,3)` cases.  These normalized kernels are intended for a subsequent
label-free lift to rectangle fibers.
-/

namespace Erdos85

/-- A canonical `(4,2)` permutation on six labelled points. -/
def finSixFourTwo : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 1 *
    (Equiv.swap 2 3 * Equiv.swap 3 4 * Equiv.swap 4 5)

theorem finSixFourTwo_cycleType : finSixFourTwo.cycleType = {2, 4} := by
  decide

/-- Our explicit commutator word. -/
def permCommutator {α : Type*} (σ τ : Equiv.Perm α) : Equiv.Perm α :=
  σ * τ * σ⁻¹ * τ⁻¹

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
/-- In the all-`(4,2)` pattern, the normalized commutator is a five-cycle. -/
theorem finSixFourTwo_allFourTwo_commutator_cycleType
    (τ : Equiv.Perm (Fin 6))
    (hτ : τ.cycleType = {2, 4})
    (hprod : (τ * finSixFourTwo).cycleType = {2, 4}) :
    (permCommutator finSixFourTwo τ).cycleType = {5} := by
  revert τ
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
/-- If the product is the unique `(3,3)` member, the normalized commutator is
either two three-cycles or one three-cycle with three fixed points. -/
theorem finSixFourTwo_productThreeThree_commutator_cycleType
    (τ : Equiv.Perm (Fin 6))
    (hτ : τ.cycleType = {2, 4})
    (hprod : (τ * finSixFourTwo).cycleType = {3, 3}) :
    (permCommutator finSixFourTwo τ).cycleType = {3, 3} ∨
      (permCommutator finSixFourTwo τ).cycleType = {3} := by
  revert τ
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
/-- If the second factor is the unique `(3,3)` member, the same 3-primary
commutator alternatives occur. -/
theorem finSixFourTwo_factorThreeThree_commutator_cycleType
    (τ : Equiv.Perm (Fin 6))
    (hτ : τ.cycleType = {3, 3})
    (hprod : (τ * finSixFourTwo).cycleType = {2, 4}) :
    (permCommutator finSixFourTwo τ).cycleType = {3, 3} ∨
      (permCommutator finSixFourTwo τ).cycleType = {3} := by
  revert τ
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 800000 in
/-- In the all-`(3,3)` pattern, the normalized commutator is the identity or
a product of two transpositions. -/
theorem finSixThreeThree_allThreeThree_commutator_cycleType
    (τ : Equiv.Perm (Fin 6))
    (hτ : τ.cycleType = {3, 3})
    (hprod : (τ * finSixThreeThree).cycleType = {3, 3}) :
    (permCommutator finSixThreeThree τ).cycleType = 0 ∨
      (permCommutator finSixThreeThree τ).cycleType = {2, 2} := by
  revert τ
  decide

end Erdos85

#print axioms Erdos85.finSixFourTwo_allFourTwo_commutator_cycleType
#print axioms Erdos85.finSixFourTwo_productThreeThree_commutator_cycleType
#print axioms Erdos85.finSixFourTwo_factorThreeThree_commutator_cycleType
#print axioms Erdos85.finSixThreeThree_allThreeThree_commutator_cycleType
