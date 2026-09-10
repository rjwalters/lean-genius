import Proofs.Erdos85OrderFortyNineThreeHighTripleCoordinateBlockCap

namespace Erdos85

theorem finset_inter_card_relabel
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (S T : Finset V) (e : V ≃ W) :
    (S.image e ∩ T.image e).card = (S ∩ T).card := by
  rw [← Finset.image_inter S T e.injective]
  exact Finset.card_image_of_injective _ e.injective

theorem encodedTripleBlockCap_relabel
    (blocks : Fin 3 → Finset (Fin 24)) (S : Finset (Fin 24))
    (e : Equiv.Perm (Fin 24)) :
    encodedTripleBlockCap (fun k => (blocks k).image e) (S.image e) =
      encodedTripleBlockCap blocks S := by
  unfold encodedTripleBlockCap
  apply Bool.decide_congr
  simp only [finset_inter_card_relabel]

/-- A permutation preserves the no-reused-pair condition between two families. -/
theorem family_inter_cap_relabel
    (F K : Finset (Finset (Fin 24))) (e : Equiv.Perm (Fin 24)) :
    (∀ S ∈ F.image (fun A => A.image e), ∀ T ∈ K.image (fun A => A.image e),
      (S ∩ T).card ≤ 1) ↔
    (∀ S ∈ F, ∀ T ∈ K, (S ∩ T).card ≤ 1) := by
  constructor
  · intro h S hS T hT
    have hh := h (S.image e) (Finset.mem_image.mpr ⟨S,hS,rfl⟩)
      (T.image e) (Finset.mem_image.mpr ⟨T,hT,rfl⟩)
    simpa only [finset_inter_card_relabel] using hh
  · intro h S hS T hT
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hT
    simpa only [finset_inter_card_relabel] using h A hA C hC

end Erdos85
#print axioms Erdos85.finset_inter_card_relabel
#print axioms Erdos85.encodedTripleBlockCap_relabel
#print axioms Erdos85.family_inter_cap_relabel
