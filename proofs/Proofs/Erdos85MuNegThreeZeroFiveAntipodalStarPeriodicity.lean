import Proofs.Erdos85MuNegThreeZeroFiveAntipodalCrossCenterOverlap

/-! # Four-periodicity of antipodal forced stars -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Opposite coordinate indices name the same two eligible incidence stars,
in the opposite order. -/
theorem h305AntipodalSaturatedStarUnion_add_four
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) (i : ZMod 8) :
    h305AntipodalSaturatedStarUnion R u (i + 4) =
      h305AntipodalSaturatedStarUnion R u i := by
  rw [h305AntipodalSaturatedStarUnion,
    h305AntipodalSaturatedStarUnion]
  have h2 : (i + 4) + 2 = i + 6 := by ring
  have h6 : (i + 4) + 6 = i + 2 := by
    have hall : ∀ i : ZMod 8, (i + 4) + 6 = i + 2 := by
      decide
    exact hall i
  rw [h2, h6, Finset.union_comm]

/-- A residual type-one target is forced by a genuinely different
antipodal center class: neither index naming the original center can be
the routing coordinate. -/
theorem h305_typeOne_outside_antipodalStar_forced_by_other_center
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V) (i : ZMod 8)
    (e : R.edgeFinset)
    (heType : e ∈ shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 1)
    (heOutside : e.1 ∉ h305AntipodalSaturatedStarUnion R u i) :
    ∃ j : ZMod 8, j ≠ i ∧ j ≠ i + 4 ∧
      e.1 ∈ h305AntipodalSaturatedStarUnion R u j := by
  obtain ⟨j, hji, hej⟩ :=
    h305_typeOne_outside_antipodalStar_forced_by_other_coordinate
      R u i e heType heOutside
  refine ⟨j, hji, ?_, hej⟩
  intro hj4
  subst j
  rw [h305AntipodalSaturatedStarUnion_add_four R u i] at hej
  exact heOutside hej

end

end Erdos85

#print axioms Erdos85.h305AntipodalSaturatedStarUnion_add_four
#print axioms
  Erdos85.h305_typeOne_outside_antipodalStar_forced_by_other_center
