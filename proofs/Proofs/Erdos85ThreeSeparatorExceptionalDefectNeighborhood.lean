import Proofs.Erdos85ThreeSeparatorExceptionalPointMatching

/-!
# The exceptional point's exact defect neighborhood

The B17 matching image consists exactly of the K-points that share an
ambient neighbor with `c`.  Consequently the unused K-points are precisely
the defect neighbors of `c`.  This is (B17').
-/

open Finset SimpleGraph

namespace Erdos85

/-- B17': if the defect neighborhood of `c` lies in `K`, the complement of
the exceptional matching image inside `K \ {c}` is exactly that defect
neighborhood. -/
theorem exceptionalPoint_defectNeighborFinset_eq_unusedK
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) (c : V) (K : Finset V)
    (hcK : c ∈ K)
    (htwo : ∀ y ∈ G.neighborFinset c,
      (G.neighborFinset y ∩ K).card = 2)
    (φ : {y // y ∈ G.neighborFinset c} ↪ V)
    (hφ : ∀ y, φ y ∈ K \ {c} ∧ G.Adj y.1 (φ y))
    (hDsub : (secondOrderDefectGraph G).neighborFinset c ⊆ K) :
    let Q := (Finset.univ : Finset {y // y ∈ G.neighborFinset c}).map φ
    (secondOrderDefectGraph G).neighborFinset c = K \ ({c} ∪ Q) := by
  dsimp only
  let D := secondOrderDefectGraph G
  let Q := (Finset.univ : Finset {y // y ∈ G.neighborFinset c}).map φ
  have hother_unique (y : {y // y ∈ G.neighborFinset c})
      {z : V} (hzK : z ∈ K) (hzc : z ≠ c) (hyz : G.Adj y.1 z) :
      z = φ y := by
    let S := G.neighborFinset y.1 ∩ K
    have hcS : c ∈ S := by
      refine Finset.mem_inter.mpr ⟨?_, hcK⟩
      exact (G.mem_neighborFinset y.1 c).mpr
        ((G.mem_neighborFinset c y.1).mp y.2).symm
    have hφS : φ y ∈ S := Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset y.1 (φ y)).mpr (hφ y).2,
        (Finset.mem_sdiff.mp (hφ y).1).1⟩
    have hzS : z ∈ S := Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset y.1 z).mpr hyz, hzK⟩
    have hsub : {c, φ y} ⊆ S := by
      intro w hw
      rcases Finset.mem_insert.mp hw with hwc | hwφ
      · simpa [hwc] using hcS
      · simpa [Finset.mem_singleton.mp hwφ] using hφS
    have hφne : φ y ≠ c := by
      intro h
      exact (Finset.mem_sdiff.mp (hφ y).1).2 (by simpa [h])
    have hpairCard : ({c, φ y} : Finset V).card = 2 := by
      simp [hφne, Ne.symm hφne]
    have hSCard : S.card = 2 := htwo y.1 y.2
    have heq : ({c, φ y} : Finset V) = S :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have hzPair : z ∈ ({c, φ y} : Finset V) := by simpa [heq] using hzS
    rcases Finset.mem_insert.mp hzPair with hzcEq | hzφ
    · exact False.elim (hzc hzcEq)
    · exact Finset.mem_singleton.mp hzφ
  apply Finset.Subset.antisymm
  · intro k hkD
    have hck : c ≠ k := by
      intro h
      subst k
      exact (secondOrderDefectGraph G).loopless.irrefl c
        (((secondOrderDefectGraph G).mem_neighborFinset c c).mp hkD)
    apply Finset.mem_sdiff.mpr
    refine ⟨hDsub hkD, ?_⟩
    intro hkUnion
    rcases Finset.mem_union.mp hkUnion with hkc | hkQ
    · exact hck (Finset.mem_singleton.mp hkc).symm
    · obtain ⟨y, -, hyk⟩ := Finset.mem_map.mp hkQ
      have hyCommon := (hφ y).2
      have hky : G.Adj k y.1 := by
        rw [← hyk]
        exact hyCommon.symm
      have hnotD := not_secondOrderDefect_adj_of_commonNeighbor
        G hfree hck
          ((G.mem_neighborFinset c y.1).mp y.2) hky
      exact hnotD (((secondOrderDefectGraph G).mem_neighborFinset c k).mp hkD)
  · intro k hkRhs
    have hkParts := Finset.mem_sdiff.mp hkRhs
    have hkcNot : k ∉ ({c} : Finset V) := by
      intro hkc
      exact hkParts.2 (Finset.mem_union.mpr (Or.inl hkc))
    have hck : c ≠ k := by
      intro h
      subst k
      exact hkcNot (Finset.mem_singleton_self c)
    have hkQNot : k ∉ Q := by
      intro hkQ
      exact hkParts.2 (Finset.mem_union.mpr (Or.inr hkQ))
    by_contra hkDNot
    have hcommon := card_common_eq_if_secondOrderDefect G hfree c k hck
    rw [if_neg hkDNot] at hcommon
    have hpos : 0 < (G.neighborFinset c ∩ G.neighborFinset k).card := by
      omega
    obtain ⟨y, hy⟩ := Finset.card_pos.mp hpos
    have hyParts := Finset.mem_inter.mp hy
    have hyc := hyParts.1
    have hyk := hyParts.2
    let y' : {y // y ∈ G.neighborFinset c} := ⟨y, hyc⟩
    have hky : G.Adj y k :=
      ((G.mem_neighborFinset k y).mp hyk).symm
    have hkφ : k = φ y' := hother_unique y' hkParts.1 hck.symm hky
    apply hkQNot
    exact Finset.mem_map.mpr ⟨y', Finset.mem_univ _, hkφ.symm⟩

#print axioms exceptionalPoint_defectNeighborFinset_eq_unusedK

end Erdos85
