import Mathlib

namespace Erdos85

/-- A set meeting each covering block at most once has at most as many vertices
as there are blocks. Neither disjointness nor a fixed block size is needed. -/
theorem card_le_covering_family_of_inter_card_le_one
    {V : Type*} [DecidableEq V] (X : Finset V) (F : Finset (Finset V))
    (hcover : X ⊆ F.biUnion id)
    (hcap : ∀ S ∈ F, (X ∩ S).card ≤ 1) : X.card ≤ F.card := by
  have hsub : X ⊆ F.biUnion (fun S => X ∩ S) := by
    intro x hx
    obtain ⟨S,hS,hxS⟩ := Finset.mem_biUnion.mp (hcover hx)
    exact Finset.mem_biUnion.mpr ⟨S,hS,Finset.mem_inter.mpr ⟨hx,hxS⟩⟩
  calc
    X.card ≤ (F.biUnion (fun S => X ∩ S)).card := Finset.card_le_card hsub
    _ ≤ ∑ S ∈ F, (X ∩ S).card := Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ F, 1 := Finset.sum_le_sum hcap
    _ = F.card := by simp

end Erdos85
#print axioms Erdos85.card_le_covering_family_of_inter_card_le_one
