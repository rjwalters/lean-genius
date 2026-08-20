import Proofs.Erdos85MuNegThreeZeroFiveAntipodalCommonTypeBalance
import Proofs.Erdos85MuNegThreeZeroFiveShoreTypePopulations

/-! # A target shared by three antipodal common-support censuses -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- If four centers each see at least seven members of a twelve-element
target class, then one target is seen by at least three centers.  This is
the double-counting interface used for the four antipodal h305 edges. -/
theorem four_seven_incidence_into_twelve_has_triple
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A : Finset α) (B : Finset β) (r : α → β → Prop)
    [DecidableRel r]
    (hA : A.card = 4) (hB : B.card = 12)
    (hlower : ∀ a ∈ A, 7 ≤ (B.filter fun b ↦ r a b).card) :
    ∃ b ∈ B, 3 ≤ (A.filter fun a ↦ r a b).card := by
  classical
  by_contra h
  push Not at h
  have hleft : 28 ≤ ∑ a ∈ A, (B.filter fun b ↦ r a b).card := by
    calc
      28 = ∑ _a ∈ A, 7 := by simp [hA]
      _ ≤ ∑ a ∈ A, (B.filter fun b ↦ r a b).card :=
        Finset.sum_le_sum fun a ha ↦ hlower a ha
  have hright : (∑ b ∈ B, (A.filter fun a ↦ r a b).card) ≤ 24 := by
    calc
      _ ≤ ∑ _b ∈ B, 2 := Finset.sum_le_sum fun b hb ↦ by
        have := h b hb
        omega
      _ = 24 := by simp [hB]
  have hdouble :
      (∑ a ∈ A, (B.filter fun b ↦ r a b).card) =
        ∑ b ∈ B, (A.filter fun a ↦ r a b).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  omega

/-- Four antipodal centers, each with seven type-zero common targets, force
a type-zero exterior edge to share a service neighbor with at least three
of the centers. -/
theorem h305_four_antipodal_centers_have_triple_typeZero_target
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (U : Finset V) (A : Finset R.edgeFinset)
    (hA : A.card = 4)
    (hzero : (shoreTypeEdgeFinset R U 0).card = 12)
    (hlower : ∀ a ∈ A,
      7 ≤ offDiagonalCommonShoreTypeCount R Cedge a U 0) :
    ∃ b ∈ shoreTypeEdgeFinset R U 0,
      3 ≤ (A.filter fun a ↦
        b ∈ offDiagonalCommonNeighborSupport Cedge a).card := by
  classical
  let B := shoreTypeEdgeFinset R U 0
  let r := fun a b : R.edgeFinset ↦
    b ∈ offDiagonalCommonNeighborSupport Cedge a
  have hB : B.card = 12 := by simpa [B] using hzero
  have hseven : ∀ a ∈ A, 7 ≤ (B.filter fun b ↦ r a b).card := by
    intro a ha
    have heq : (B.filter fun b ↦ r a b) =
        (offDiagonalCommonNeighborSupport Cedge a).filter fun b ↦
          (b.1.toFinset ∩ U).card = 0 := by
      ext b
      simp [B, r, shoreTypeEdgeFinset, and_comm]
    rw [heq]
    exact hlower a ha
  exact four_seven_incidence_into_twelve_has_triple A B r hA hB hseven

end

end Erdos85

#print axioms Erdos85.four_seven_incidence_into_twelve_has_triple
#print axioms Erdos85.h305_four_antipodal_centers_have_triple_typeZero_target
