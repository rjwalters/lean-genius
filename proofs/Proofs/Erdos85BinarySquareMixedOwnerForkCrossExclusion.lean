import Proofs.Erdos85BinarySquareMixedOwnerCanonicalForkCenters

/-! # Cross-color exclusions in a mixed-owner fork -/

open SimpleGraph

namespace Erdos85

noncomputable section

private theorem cross_chord_forbidden_of_two_commonNeighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G)
    {p q u v : V} (hpq : p ≠ q) (huv : u ≠ v)
    (hpu : G.Adj p u) (hqu : G.Adj q u) (hqv : G.Adj q v) :
    ¬ G.Adj p v := by
  intro hpv
  have hu : u ∈ G.neighborFinset p ∩ G.neighborFinset q := by
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset p u).mpr hpu,
        (G.mem_neighborFinset q u).mpr hqu⟩
  have hv : v ∈ G.neighborFinset p ∩ G.neighborFinset q := by
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset p v).mpr hpv,
        (G.mem_neighborFinset q v).mpr hqv⟩
  exact huv (Finset.card_le_one.mp
    (card_inter_neighborFinset_le_one hfree hpq) u hu v hv)

/-- At one closing of a mixed-owner fork, each canonical center avoids the
opposite root.  These exclusions retain the coupling between the two route
colors; they do not follow from either routing row in isolation. -/
theorem mixedOwnerClosing_crossCenter_exclusion
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e f b c : (secondOrderDefectGraph G).ConnectedComponent}
    (hef : e ≠ f) (hdf : d ≠ f) (hbc : b ≠ c)
    (x : d.supp) (y : e.supp) (z : f.supp)
    (hby : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z.1)
    (hcx : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z.1 x.1) :
    let ub := crossCommonNeighbor G hfree hef y z
    let uc := crossCommonNeighbor G hfree hdf x z
    ¬ G.Adj x.1 ub ∧ ¬ G.Adj y.1 uc := by
  classical
  let D := secondOrderDefectGraph G
  let ub := crossCommonNeighbor G hfree hef y z
  let uc := crossCommonNeighbor G hfree hdf x z
  have hrb : crossIntermediateComponent G hfree hef y z = b :=
    crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hef y z b hby
  have hrc : crossIntermediateComponent G hfree hdf x z = c := by
    rw [crossIntermediateComponent_reverse G hfree hdf x z]
    exact crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hdf.symm z x c hcx
  have hubcomp : D.connectedComponentMk ub = b := by
    rw [← hrb]
    exact (ConnectedComponent.mem_supp_iff _ _).mp
      (crossCommonNeighbor_mem_intermediate G hfree hef y z)
  have huccomp : D.connectedComponentMk uc = c := by
    rw [← hrc]
    exact (ConnectedComponent.mem_supp_iff _ _).mp
      (crossCommonNeighbor_mem_intermediate G hfree hdf x z)
  have hubuc : ub ≠ uc := by
    intro h
    exact hbc (hubcomp.symm.trans ((congrArg D.connectedComponentMk h).trans huccomp))
  have hxz : x.1 ≠ z.1 := by
    intro h
    apply hdf
    have hxcomp := (ConnectedComponent.mem_supp_iff d x.1).mp x.2
    have hzcomp := (ConnectedComponent.mem_supp_iff f z.1).mp z.2
    exact hxcomp.symm.trans ((congrArg D.connectedComponentMk h).trans hzcomp)
  have hyz : y.1 ≠ z.1 := by
    intro h
    apply hef
    have hycomp := (ConnectedComponent.mem_supp_iff e y.1).mp y.2
    have hzcomp := (ConnectedComponent.mem_supp_iff f z.1).mp z.2
    exact hycomp.symm.trans ((congrArg D.connectedComponentMk h).trans hzcomp)
  change ¬ G.Adj x.1 ub ∧ ¬ G.Adj y.1 uc
  constructor
  · exact cross_chord_forbidden_of_two_commonNeighbors G hfree hxz hubuc.symm
      (crossCommonNeighbor_spec G hfree hdf x z).1
      (crossCommonNeighbor_spec G hfree hdf x z).2
      (crossCommonNeighbor_spec G hfree hef y z).2
  · exact cross_chord_forbidden_of_two_commonNeighbors G hfree hyz hubuc
      (crossCommonNeighbor_spec G hfree hef y z).1
      (crossCommonNeighbor_spec G hfree hef y z).2
      (crossCommonNeighbor_spec G hfree hdf x z).2

/-- Both closings in a mixed-owner fork satisfy the four cross-color
nonadjacencies simultaneously. -/
theorem ownerFork_crossCenter_exclusions
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {d e f₁ f₂ b c : (secondOrderDefectGraph G).ConnectedComponent}
    (hef₁ : e ≠ f₁) (hef₂ : e ≠ f₂)
    (hdf₁ : d ≠ f₁) (hdf₂ : d ≠ f₂) (hbc : b ≠ c)
    (x : d.supp) (y : e.supp) (z₁ : f₁.supp) (z₂ : f₂.supp)
    (hby₁ : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z₁.1)
    (hby₂ : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y.1 z₂.1)
    (hcx₁ : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z₁.1 x.1)
    (hcx₂ : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z₂.1 x.1) :
    let ub₁ := crossCommonNeighbor G hfree hef₁ y z₁
    let ub₂ := crossCommonNeighbor G hfree hef₂ y z₂
    let uc₁ := crossCommonNeighbor G hfree hdf₁ x z₁
    let uc₂ := crossCommonNeighbor G hfree hdf₂ x z₂
    ¬ G.Adj x.1 ub₁ ∧ ¬ G.Adj x.1 ub₂ ∧
      ¬ G.Adj y.1 uc₁ ∧ ¬ G.Adj y.1 uc₂ := by
  have h₁ := mixedOwnerClosing_crossCenter_exclusion
    G hfree hef₁ hdf₁ hbc x y z₁ hby₁ hcx₁
  have h₂ := mixedOwnerClosing_crossCenter_exclusion
    G hfree hef₂ hdf₂ hbc x y z₂ hby₂ hcx₂
  exact ⟨h₁.1, h₂.1, h₁.2, h₂.2⟩

end

end Erdos85
