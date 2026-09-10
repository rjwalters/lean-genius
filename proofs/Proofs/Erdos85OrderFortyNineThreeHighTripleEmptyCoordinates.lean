import Proofs.Erdos85InsertTwoBlockLabels
import Proofs.Erdos85OrderFortyNineThreeHighTripleSecondaryPartition

namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_empty_coordinates
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z)
    (lU : Fin 15 ≃ (↑(threeHighTripleSpecialUnion G z) : Set (Fin 49)))
    (lR : Fin 8 ≃ (↑(threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)) : Set (Fin 49))) :
    ∃ e : Fin 24 ≃ (↑(threeHighTripleEmptySet G) : Set (Fin 49)),
      (∀ i, (e (Fin.castAdd 1 (Fin.castAdd 8 i))).val = (lU i).val) ∧
      (e 23).val = u ∧
      (∀ j, (e (Fin.castAdd 1 (Fin.natAdd 15 j))).val = (lR j).val) ∧
      (∀ i, ¬ G.Adj (e 23).val (e (Fin.castAdd 1 (Fin.castAdd 8 i))).val) := by
  classical
  let E := threeHighTripleEmptySet G
  let U := threeHighTripleSpecialUnion G z
  let R := E \ insert u U
  have huU : u ∉ U := threeHigh_triple_root_empty_outside_special_union
    G hfree hmin hHigh hone z hz hu huz
  have huR : u ∉ R := by simp [R]
  have hUR : Disjoint U R := by
    apply Finset.disjoint_left.mpr
    intro x hx hxr
    exact (Finset.mem_sdiff.mp hxr).2 (Finset.mem_insert_of_mem hx)
  have hsub : insert u U ⊆ E := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hu
    · obtain ⟨s, hs, hx⟩ := Finset.mem_biUnion.mp hx
      exact (Finset.mem_inter.mp hx).2
  have hE : E = (U ∪ R) ∪ {u} := by
    have hp := Finset.union_sdiff_of_subset hsub
    simpa only [Finset.union_singleton, Finset.insert_union] using hp.symm
  obtain ⟨e, heU, heR, heu⟩ := insert_two_block_labels U R E u huU huR hUR hE lU lR
  have he23 : (e 23).val = u := heu
  refine ⟨e, heU, he23, heR, ?_⟩
  intro i
  rw [he23, heU]
  exact threeHigh_triple_root_empty_no_special_union_edge G hfree hmin hHigh hone z hz hu huz (lU i).property

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_empty_coordinates
