import Proofs.Erdos85EdgeIndexedServiceMiddleProfileParity
import Proofs.Erdos85MuNegThreeZeroFiveCorrectShoreGeometry
import Proofs.Erdos85MuNegThreeZeroFiveServiceShoreTypeProfiles

/-! # Graph-facing middle-profile parity for h305 shores -/

open Finset SimpleGraph Matrix

namespace Erdos85

noncomputable section

/-- Every type-two edge of a corrected h305 shore is a labeled coordinate
pair at one of the five eligible offsets. -/
theorem h305_typeTwoEdge_exists_coordinate_endpoints
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj]
    (u : ZMod 8 → V)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u)
    (a : R.edgeFinset)
    (ha : a ∈ shoreTypeEdgeFinset R
      ((Finset.univ : Finset (ZMod 8)).image u) 2) :
    ∃ i j : ZMod 8,
      a.1.toFinset = {u i, u j} ∧
      (j - i = 1 ∨ j - i = 3 ∨ j - i = 4 ∨
        j - i = 5 ∨ j - i = 7) := by
  classical
  rcases a with ⟨a, haR⟩
  induction a using Sym2.inductionOn with
  | _ x y =>
    let U := (Finset.univ : Finset (ZMod 8)).image u
    have hinter : (({x, y} : Finset V) ∩ U).card = 2 := by
      simpa [U, Sym2.toFinset_mk_eq] using (Finset.mem_filter.mp ha).2
    have hedgeCard : ({x, y} : Finset V).card = 2 := by
      simpa [Sym2.toFinset_mk_eq] using
        R.card_toFinset_mem_edgeFinset ⟨s(x, y), haR⟩
    have hsubset : ({x, y} : Finset V) ⊆ U := by
      have hsub : ({x, y} : Finset V) ∩ U ⊆ ({x, y} : Finset V) :=
        Finset.inter_subset_left
      have heq : ({x, y} : Finset V) ∩ U = {x, y} :=
        Finset.eq_of_subset_of_card_le hsub (by rw [hinter, hedgeCard])
      intro z hz
      exact (Finset.mem_inter.mp (heq.symm ▸ hz)).2
    have hxU : x ∈ U := hsubset (by simp)
    have hyU : y ∈ U := hsubset (by simp)
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hxU
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hyU
    have hadj : R.Adj (u i) (u j) := R.mem_edgeFinset.mp haR
    refine ⟨i, j, Sym2.toFinset_mk_eq, ?_⟩
    rcases hmode with htri | htf
    · rcases (htri i j).mp hadj with h1 | h4 | h7
      · exact Or.inl h1
      · exact Or.inr (Or.inr (Or.inl h4))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h7)))
    · rcases (htf i j).mp hadj with h3 | h4 | h5
      · exact Or.inr (Or.inl h3)
      · exact Or.inr (Or.inr (Or.inl h4))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h5)))

/-- On either corrected h305 shore, the number of central type-two edges
having the middle same-type service count `1` is even. -/
theorem h305_typeTwo_middleProfile_even
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (hCreg : ∀ b, Cedge.degree b = 6)
    (u v : ZMod 8 → V)
    (huinj : Function.Injective u) (hvinj : Function.Injective v)
    (hu : ∀ z, H.neighborFinset (u z) = {u (z - 1), u (z + 1)})
    (hdisj : ∀ k l, u k ≠ v l)
    (hcover : ∀ x : V, (∃ k, x = u k) ∨ ∃ l, x = v l)
    (hmode : MuNegThreeZeroFiveTriangleShoreMode R u ∨
      MuNegThreeZeroFiveTfShoreMode R u) :
    let U := (Finset.univ : Finset (ZMod 8)).image u
    Even ((shoreTypeEdgeFinset R U 2).filter fun a ↦
      serviceNeighborShoreTypeCount R Cedge a U 2 = 1).card := by
  classical
  dsimp only
  let U := (Finset.univ : Finset (ZMod 8)).image u
  apply serviceNeighborShoreTypeCount_middle_profile_even R Cedge U 2
  intro a ha
  obtain ⟨i, j, haij, hoffset⟩ :=
    h305_typeTwoEdge_exists_coordinate_endpoints R u hmode a ha
  have hp := h305_serviceNeighbor_shoreType_profiles H R Cedge hservice
    hCreg u v huinj hvinj hu hdisj hcover a i j haij hoffset
  rcases hp with hp | hp | hp
  · exact Or.inl hp.1
  · exact Or.inr (Or.inl hp.1)
  · exact Or.inr (Or.inr hp.1)

end

end Erdos85

#print axioms Erdos85.h305_typeTwoEdge_exists_coordinate_endpoints
#print axioms Erdos85.h305_typeTwo_middleProfile_even
