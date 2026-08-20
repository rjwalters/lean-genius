import Proofs.Erdos85EdgeIndexedServiceMatchingLaw
import Proofs.Erdos85C4FreeRegularCommonSupport

/-! # Packing the witnesses of several service common-target relations -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- Common-target membership can be witnessed coherently.  Distinct chosen
witnesses are neighbors of the same service vertex, so the service matching
law forces their exterior endpoint pairs to be disjoint.  Coincident chosen
witnesses, on the other hand, are a single service edge adjacent to several
centers. -/
theorem edgeIndexedService_exists_commonWitnessPacking
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (A : Finset R.edgeFinset) (b : R.edgeFinset)
    (hcommon : ∀ a ∈ A,
      b ∈ offDiagonalCommonNeighborSupport Cedge a) :
    ∃ w : ↥(A : Set R.edgeFinset) → R.edgeFinset,
      (∀ a, Cedge.Adj b (w a) ∧ Cedge.Adj a.1 (w a)) ∧
      ∀ a d, w a ≠ w d →
        Disjoint (w a).1.toFinset (w d).1.toFinset := by
  classical
  have hex : ∀ a : ↥(A : Set R.edgeFinset),
      ∃ c : R.edgeFinset, Cedge.Adj b c ∧ Cedge.Adj a.1 c := by
    intro a
    have hb := hcommon a.1 a.2
    rw [offDiagonalCommonNeighborSupport] at hb
    have hn := (Finset.mem_filter.mp hb).2
    obtain ⟨c, hc⟩ := hn
    have hc' := Finset.mem_inter.mp hc
    exact ⟨c,
      (Cedge.mem_neighborFinset b c).mp hc'.1,
      (Cedge.mem_neighborFinset a.1 c).mp hc'.2⟩
  choose w hw using hex
  refine ⟨w, hw, ?_⟩
  intro a d had
  exact edgeIndexedService_neighborEdges_pairwiseDisjoint
    H R Cedge hservice b (w a) (w d) (hw a).1 (hw d).1 had

/-- If at least three centers share a common target, three such centers can
be selected together with packed common-neighbor witnesses. -/
theorem edgeIndexedService_exists_three_commonWitnesses
    {V : Type*} [Fintype V] [DecidableEq V]
    (H R : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel R.Adj]
    (Cedge : SimpleGraph R.edgeFinset) [DecidableRel Cedge.Adj]
    (hservice : EdgeIndexedServiceEquation H R Cedge)
    (A : Finset R.edgeFinset) (b : R.edgeFinset)
    (hthree : 3 ≤ (A.filter fun a ↦
      b ∈ offDiagonalCommonNeighborSupport Cedge a).card) :
    ∃ S : Finset R.edgeFinset, S ⊆ A ∧ S.card = 3 ∧
      ∃ w : ↥(S : Set R.edgeFinset) → R.edgeFinset,
        (∀ a, Cedge.Adj b (w a) ∧ Cedge.Adj a.1 (w a)) ∧
        ∀ a d, w a ≠ w d →
          Disjoint (w a).1.toFinset (w d).1.toFinset := by
  classical
  let T := A.filter fun a ↦
    b ∈ offDiagonalCommonNeighborSupport Cedge a
  obtain ⟨S, hST, hScard⟩ := Finset.exists_subset_card_eq hthree
  have hSA : S ⊆ A := fun a ha ↦
    (Finset.mem_filter.mp (hST ha)).1
  have hcommon : ∀ a ∈ S,
      b ∈ offDiagonalCommonNeighborSupport Cedge a := fun a ha ↦
    (Finset.mem_filter.mp (hST ha)).2
  refine ⟨S, hSA, hScard, ?_⟩
  exact edgeIndexedService_exists_commonWitnessPacking
    H R Cedge hservice S b hcommon

end

end Erdos85

#print axioms Erdos85.edgeIndexedService_exists_commonWitnessPacking
#print axioms Erdos85.edgeIndexedService_exists_three_commonWitnesses
