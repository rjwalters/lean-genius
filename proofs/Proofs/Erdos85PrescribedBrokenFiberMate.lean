import Proofs.Erdos85DisjointFiberInvolutionGluing
import Proofs.Erdos85PrescribedPairInvolution

/-!
# Canonical plus owner-prescribed broken-fiber pairing

This composes the two Baer relay primitives: retain the canonical involution
on one fiber, and pair the disjoint even broken fiber while forcing the
owner-determined pair `a ↔ b`.
-/

namespace Erdos85

noncomputable section

/-- A canonical local involution extends across a disjoint even broken fiber
without changing canonical pairs and while realizing one prescribed broken
pair. -/
theorem exists_gluedMate_with_prescribed_broken_pair
    {V : Type*} [Fintype V] [DecidableEq V]
    (S T : Finset V) (hdisjoint : Disjoint S T)
    (left : V → V)
    (hleftClosed : ∀ v, v ∈ S → left v ∈ S)
    (hleftInvol : ∀ v, v ∈ S → left (left v) = v)
    (hleftFixed : ∀ v, v ∈ S → left v ≠ v)
    (a b : V) (hevenT : Even T.card) (hab : a ≠ b)
    (haT : a ∈ T) (hbT : b ∈ T) :
    ∃ mate : V → V,
      mate a = b ∧ mate b = a ∧
      (∀ v, v ∈ S → mate v = left v) ∧
      (∀ v, v ∈ S → mate v ∈ S) ∧
      (∀ v, v ∈ T → mate v ∈ T) ∧
      (∀ v, v ∈ S ∪ T → mate (mate v) = v) ∧
      ∀ v, v ∈ S ∪ T → mate v ≠ v := by
  obtain ⟨right, hra, hrb, hrightClosed, hrightInvol, hrightFixed, _⟩ :=
    exists_mate_of_even_finset_with_prescribed_pair
      T a b hevenT hab haT hbT
  let mate := glueDisjointFiberMate S left right
  have hspec := glueDisjointFiberMate_spec S T hdisjoint left right
    hleftClosed hleftInvol hleftFixed
    hrightClosed hrightInvol hrightFixed
  refine ⟨mate, ?_, ?_, hspec.1, hspec.2.2.1, hspec.2.2.2.1,
    hspec.2.2.2.2.1, hspec.2.2.2.2.2⟩
  · have haNS : a ∉ S := fun haS =>
      Finset.disjoint_left.mp hdisjoint haS haT
    simp [mate, glueDisjointFiberMate, haNS, hra]
  · have hbNS : b ∉ S := fun hbS =>
      Finset.disjoint_left.mp hdisjoint hbS hbT
    simp [mate, glueDisjointFiberMate, hbNS, hrb]

#print axioms exists_gluedMate_with_prescribed_broken_pair

end

end Erdos85
