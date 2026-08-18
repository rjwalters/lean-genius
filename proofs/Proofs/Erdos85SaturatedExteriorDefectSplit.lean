import Proofs.Erdos85ExteriorDefectDecomposition
import Proofs.Erdos85MinimumLayerDefectCover

/-!
# Owner fibers in the saturated exterior

The general exterior-defect decomposition adds an edge exactly when two
exterior vertices share a deleted neighbor.  In a saturated minimum layer,
the deleted common-neighbor relation is exactly equality of the canonical
owner projection.  Combining the theorem below with
`finsetExterior_secondOrderDefect_adj_iff` gives the graph identity
`D_ext = D_parent|ext + CᵀC - I`.
-/

namespace Erdos85

noncomputable section

/-- In a saturated minimum layer, two exterior vertices share a child
neighbor if and only if they have the same owner. -/
theorem exists_minimumLayer_saturated_owner_commonNeighbor_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3) :
    ∃ owner : minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀ →
        minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (∀ z, z.1 ∈ minimumLayerExternalNeighborFinset G
        (secondOrderDefectGraph G) c₀ (owner z)) ∧
      ∀ z w,
        (∃ u ∈ minimumLayerImageFinset (secondOrderDefectGraph G) c₀,
          G.Adj z.1 u ∧ G.Adj w.1 u) ↔ owner z = owner w := by
  classical
  let D := secondOrderDefectGraph G
  let X := minimumLayerExteriorVertex D c₀
  let E := minimumLayerExternalNeighborFinset G D c₀
  obtain ⟨owner, hownerMem, _hmap, _hlift⟩ :=
    exists_minimumLayer_saturated_defectCover
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree hd heven hmin hcard c₀ hregChild hcardChild
  refine ⟨owner, hownerMem, ?_⟩
  intro z w
  constructor
  · rintro ⟨u, huLayer, hzu, hwu⟩
    rw [minimumLayerImageFinset] at huLayer
    obtain ⟨a, _ha, hau⟩ := Finset.mem_image.mp huLayer
    change a.2.1 = u at hau
    have hza : z.1 ∈ E a := by
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, z.2⟩
      apply (G.mem_neighborFinset a.2.1 z.1).mpr
      rw [hau]
      exact hzu.symm
    have hwa : w.1 ∈ E a := by
      apply Finset.mem_sdiff.mpr
      refine ⟨?_, w.2⟩
      apply (G.mem_neighborFinset a.2.1 w.1).mpr
      rw [hau]
      exact hwu.symm
    have haz : a = owner z := by
      by_contra hne
      have hdj := hpair (Finset.mem_univ a)
        (Finset.mem_univ (owner z)) hne
      exact (Finset.disjoint_left.mp hdj hza (hownerMem z)).elim
    have haw : a = owner w := by
      by_contra hne
      have hdj := hpair (Finset.mem_univ a)
        (Finset.mem_univ (owner w)) hne
      exact (Finset.disjoint_left.mp hdj hwa (hownerMem w)).elim
    exact haz.symm.trans haw
  · intro how
    refine ⟨(owner z).2.1, ?_, ?_, ?_⟩
    · rw [minimumLayerImageFinset]
      exact Finset.mem_image.mpr ⟨owner z, Finset.mem_univ _, rfl⟩
    · exact ((G.mem_neighborFinset (owner z).2.1 z.1).mp
        (Finset.mem_sdiff.mp (hownerMem z)).1).symm
    · rw [how]
      exact ((G.mem_neighborFinset (owner w).2.1 w.1).mp
        (Finset.mem_sdiff.mp (hownerMem w)).1).symm

/-- The canonical owner fibers all have the expected external-neighborhood
size `d-s`; in the residual case this is `112`. -/
theorem exists_minimumLayer_saturated_owner_uniformFiber
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬containsC4 V G) {d s : ℕ}
    (hd : 4 ≤ d) (heven : Even d) (hmin : d ≤ G.minDegree)
    (hcard : Fintype.card V = d * (d - 1) + 3)
    (c₀ : (secondOrderDefectGraph G).ConnectedComponent)
    (hregChild : ∀ x : minimumLayerVertex (secondOrderDefectGraph G) c₀,
      (minimumLayerGraph G (secondOrderDefectGraph G) c₀).degree x = s)
    (hcardChild :
      Fintype.card (minimumLayerVertex (secondOrderDefectGraph G) c₀) =
        s * (s - 1) + 3)
    (hspos : 0 < s) (hsd : s < d)
    (hsat : d = (s - 1) * (s - 1) + 3) :
    ∃ owner : minimumLayerExteriorVertex (secondOrderDefectGraph G) c₀ →
        minimumLayerVertex (secondOrderDefectGraph G) c₀,
      ∀ a, (Finset.univ.filter fun z => owner z = a).card = d - s := by
  classical
  let D := secondOrderDefectGraph G
  let E := minimumLayerExternalNeighborFinset G D c₀
  obtain ⟨owner, hownerMem, _hcommon⟩ :=
    exists_minimumLayer_saturated_owner_commonNeighbor_iff
      G hfree hd heven hmin hcard c₀ hregChild hcardChild hspos hsd hsat
  have hpair := minimumLayer_externalNeighbor_pairwiseDisjoint
    G hfree hd heven hmin hcard c₀ hregChild hcardChild
  have hbelow : Fintype.card V < (d + 1) * (d - 1) + 1 := by
    rw [hcard]
    obtain ⟨t, rfl⟩ : ∃ t : ℕ, d = t + 4 := ⟨d - 4, by omega⟩
    norm_num
    nlinarith
  have hregParent : ∀ v : V, G.degree v = d :=
    regular_of_minDegree_card_lt_nextMooreLayer
      G hfree (by omega) hmin hbelow
  refine ⟨owner, ?_⟩
  intro a
  calc
    (Finset.univ.filter fun z => owner z = a).card = (E a).card := by
      apply Finset.card_bij (fun z _ => z.1)
      · intro z hz
        have hza : owner z = a := (Finset.mem_filter.mp hz).2
        simpa [hza] using hownerMem z
      · intro z₁ _ z₂ _ heq
        exact Subtype.ext heq
      · intro y hy
        have hyOut : y ∉ minimumLayerImageFinset D c₀ :=
          (Finset.mem_sdiff.mp hy).2
        let z : minimumLayerExteriorVertex D c₀ := ⟨y, hyOut⟩
        have hza : owner z = a := by
          by_contra hne
          have hdj := hpair (Finset.mem_univ (owner z))
            (Finset.mem_univ a) hne
          exact (Finset.disjoint_left.mp hdj (hownerMem z) hy).elim
        refine ⟨z, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hza⟩
    _ = d - s := card_minimumLayerExternalNeighborFinset
      G D c₀ hregParent hregChild a

end

end Erdos85
