import Proofs.Erdos85OrderFortyNineThreeHighTripleNeighborCoordinates

/-! Label the secondary set by six canonical matching neighbors and two far vertices. -/
namespace Erdos85
open SimpleGraph
noncomputable section

theorem threeHigh_triple_secondary_coordinates
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3)
    {u : Fin 49} (hu : u ∈ threeHighTripleEmptySet G) (huz : G.Adj u z) :
    let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
    let R := threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)
    let m := (G.induce (↑N : Set (Fin 49))).edgeFinset.card
    ∃ l : Fin 8 ≃ (↑R : Set (Fin 49)),
      (∀ i : Fin 6, (l (Fin.castAdd 2 i)).val ∈ N) ∧
      (∀ j : Fin 2, (l (Fin.natAdd 6 j)).val ∈ R \ N) ∧
      (∀ i j : Fin 6, G.Adj (l (Fin.castAdd 2 i)).val (l (Fin.castAdd 2 j)).val ↔
        matchingFinSixAdj m i j) := by
  classical
  let N := G.neighborFinset u ∩ threeHighTripleEmptySet G
  let R := threeHighTripleEmptySet G \ insert u (threeHighTripleSpecialUnion G z)
  let T := R \ N
  have hp := threeHigh_triple_secondary_partition G hfree hmin hHigh hone z hz hu huz
  have hNR : N ⊆ R := hp.2.2.2.1
  have hTc : T.card = 2 := hp.2.2.2.2.2
  have hTcard : Fintype.card (↑T : Set (Fin 49)) = 2 := by simpa using hTc
  obtain ⟨n, hmlo, hmhi, hn⟩ := threeHigh_triple_neighbor_matching_coordinates
    G hfree hmin hHigh hone z hz hu huz
  let t : Fin 2 ≃ (↑T : Set (Fin 49)) := (Fintype.equivFinOfCardEq hTcard).symm
  have hd : Disjoint N T := by
    apply Finset.disjoint_left.mpr
    intro x hx ht
    exact (Finset.mem_sdiff.mp ht).2 hx
  have hun : N ∪ T = R := Finset.union_sdiff_of_subset hNR
  have hs : (↑(N ∪ T) : Set (Fin 49)) = (↑R : Set (Fin 49)) := congrArg (fun S : Finset (Fin 49) => (↑S : Set (Fin 49))) hun
  let j : ((↑N : Set (Fin 49)) ⊕ (↑T : Set (Fin 49))) ≃ (↑R : Set (Fin 49)) :=
    (Equiv.Finset.union N T hd).trans (Equiv.setCongr hs)
  let l : Fin 8 ≃ (↑R : Set (Fin 49)) :=
    (finSumFinEquiv.symm.trans (Equiv.sumCongr n t)).trans j
  have hlN (i : Fin 6) : (l (Fin.castAdd 2 i)).val = (n i).val := by
    dsimp only [l, Equiv.trans_apply]
    rw [finSumFinEquiv_symm_apply_castAdd]
    rfl
  have hlT (i : Fin 2) : (l (Fin.natAdd 6 i)).val = (t i).val := by
    dsimp only [l, Equiv.trans_apply]
    rw [finSumFinEquiv_symm_apply_natAdd]
    rfl
  refine ⟨l, ?_, ?_, ?_⟩
  · intro i
    rw [hlN]
    exact (n i).property
  · intro i
    rw [hlT]
    exact (t i).property
  · intro i j
    rw [hlN, hlN]
    exact hn i j

end
end Erdos85
#print axioms Erdos85.threeHigh_triple_secondary_coordinates
