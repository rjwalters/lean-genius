import Proofs.Erdos85BinarySquareMixedOwnerCanonicalForkCenters

/-! # Selector exhaustion in the coincident-center fork branch -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If the canonical `c`-side centers of a fork coincide, its two canonical
`b`-side centers are distinct and exactly exhaust the size-two `b` selector
of the shared middle vertex. -/
theorem ownerFork_coincident_cCenters_canonical_bSelector_exhaustion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e f₁ f₂ b c :
      (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hef₁ : e ≠ f₁) (hef₂ : e ≠ f₂)
    (hdf₁ : d ≠ f₁) (hdf₂ : d ≠ f₂) (hbc : b ≠ c)
    (x : d.supp) (y : e.supp) (z₁ : f₁.supp) (z₂ : f₂.supp)
    (hz : z₁.1 ≠ z₂.1)
    (hby₁ : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z₁.1)
    (hby₂ : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z₂.1)
    (hcx₁ : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z₁.1 x.1)
    (hcx₂ : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z₂.1 x.1)
    (hcoincide : crossCommonNeighbor G hfree hdf₁ x z₁ =
      crossCommonNeighbor G hfree hdf₂ x z₂)
    (hbcard : (componentNeighborFinset G (secondOrderDefectGraph G) b y.1).card = 2) :
    let ub₁ := crossCommonNeighbor G hfree hef₁ y z₁
    let ub₂ := crossCommonNeighbor G hfree hef₂ y z₂
    ub₁ ≠ ub₂ ∧
      componentNeighborFinset G (secondOrderDefectGraph G) b y.1 = {ub₁, ub₂} := by
  classical
  let D := secondOrderDefectGraph G
  let ub₁ := crossCommonNeighbor G hfree hef₁ y z₁
  let ub₂ := crossCommonNeighbor G hfree hef₂ y z₂
  have hsep := ownerFork_canonicalCenter_separation G hfree hde hef₁ hef₂
    hdf₁ hdf₂ hbc x y z₁ z₂ hz hby₁ hby₂ hcx₁ hcx₂
  change ub₁ ≠ ub₂ ∨
    crossCommonNeighbor G hfree hdf₁ x z₁ ≠
      crossCommonNeighbor G hfree hdf₂ x z₂ at hsep
  have hub : ub₁ ≠ ub₂ := hsep.resolve_right (not_ne_iff.mpr hcoincide)
  have hrb₁ : crossIntermediateComponent G hfree hef₁ y z₁ = b :=
    crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hef₁ y z₁ b hby₁
  have hrb₂ : crossIntermediateComponent G hfree hef₂ y z₂ = b :=
    crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hef₂ y z₂ b hby₂
  have hub₁comp : D.connectedComponentMk ub₁ = b := by
    rw [← hrb₁]
    exact (ConnectedComponent.mem_supp_iff _ _).mp
      (crossCommonNeighbor_mem_intermediate G hfree hef₁ y z₁)
  have hub₂comp : D.connectedComponentMk ub₂ = b := by
    rw [← hrb₂]
    exact (ConnectedComponent.mem_supp_iff _ _).mp
      (crossCommonNeighbor_mem_intermediate G hfree hef₂ y z₂)
  have hub₁mem : ub₁ ∈ componentNeighborFinset G D b y.1 := by
    rw [componentNeighborFinset, Finset.mem_filter]
    exact ⟨(G.mem_neighborFinset y.1 ub₁).mpr
      (crossCommonNeighbor_spec G hfree hef₁ y z₁).1, hub₁comp⟩
  have hub₂mem : ub₂ ∈ componentNeighborFinset G D b y.1 := by
    rw [componentNeighborFinset, Finset.mem_filter]
    exact ⟨(G.mem_neighborFinset y.1 ub₂).mpr
      (crossCommonNeighbor_spec G hfree hef₂ y z₂).1, hub₂comp⟩
  refine ⟨hub, ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl
    · exact hub₁mem
    · exact hub₂mem
  · rw [hbcard]
    change 2 ≤ ({ub₁, ub₂} : Finset V).card
    simp [hub]

end

end Erdos85
