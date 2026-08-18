import Proofs.Erdos85BinarySquareOwnerBlockUnorderedClosing
import Proofs.Erdos85BinarySquareMixedOwnerCanonicalForkCenters

/-! # Canonical-center geometry of an opposite-owner bowtie -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The canonical common neighbor of a cross-component pair belongs to the
component which owns that pair. -/
theorem crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {c f owner : (secondOrderDefectGraph G).ConnectedComponent}
    (hcf : c ≠ f) (x : c.supp) (y : f.supp)
    (howner : (componentOwnerGraph G (secondOrderDefectGraph G) owner).Adj
      x.1 y.1) :
    crossCommonNeighbor G hfree hcf x y ∈ owner.supp := by
  have hr : crossIntermediateComponent G hfree hcf x y = owner :=
    crossIntermediateComponent_eq_owner_of_componentOwnerGraph_adj
      G hfree hcf x y owner howner
  rw [← hr]
  exact crossCommonNeighbor_mem_intermediate G hfree hcf x y

/-- Four alternating owner edges around a cross-component bowtie have four
pairwise-distinct canonical centers. -/
theorem oppositeOwnerBowtie_canonicalCenter_separation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {c f a b : (secondOrderDefectGraph G).ConnectedComponent}
    (hcf : c ≠ f) (hac : a ≠ c) (hbc : b ≠ c) (hab : a ≠ b)
    (x z : c.supp) (y₁ y₂ : f.supp)
    (hAxy₁ : (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj x.1 y₁.1)
    (hBy₁z : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y₁.1 z.1)
    (hAzy₂ : (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj z.1 y₂.1)
    (hBy₂x : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y₂.1 x.1)
    (hCxz : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z.1 x.1) :
    let u₁ := crossCommonNeighbor G hfree hcf x y₁
    let v₁ := crossCommonNeighbor G hfree hcf z y₁
    let u₂ := crossCommonNeighbor G hfree hcf z y₂
    let v₂ := crossCommonNeighbor G hfree hcf x y₂
    u₁ ≠ u₂ ∧ v₁ ≠ v₂ ∧
      u₁ ≠ v₁ ∧ u₁ ≠ v₂ ∧ u₂ ≠ v₁ ∧ u₂ ≠ v₂ := by
  classical
  let D := secondOrderDefectGraph G
  let u₁ := crossCommonNeighbor G hfree hcf x y₁
  let v₁ := crossCommonNeighbor G hfree hcf z y₁
  let u₂ := crossCommonNeighbor G hfree hcf z y₂
  let v₂ := crossCommonNeighbor G hfree hcf x y₂
  have hu₁mem : u₁ ∈ a.supp :=
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
      G hfree hcf x y₁ hAxy₁
  have hv₁mem : v₁ ∈ b.supp :=
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj G hfree hcf z y₁
      (by exact ((componentOwnerGraph G D b).adj_comm z.1 y₁.1).mpr hBy₁z)
  have hu₂mem : u₂ ∈ a.supp :=
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
      G hfree hcf z y₂ hAzy₂
  have hv₂mem : v₂ ∈ b.supp :=
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj G hfree hcf x y₂
      (by exact ((componentOwnerGraph G D b).adj_comm x.1 y₂.1).mpr hBy₂x)
  have hsameColorA : u₁ ≠ u₂ := by
    intro huu
    have hAxz : (componentOwnerGraph G D a).Adj z.1 x.1 := by
      rw [componentOwnerGraph_adj]
      refine ⟨fun h => (componentOwnerGraph_adj G D c z.1 x.1).mp hCxz |>.1 h, ?_⟩
      refine ⟨u₁, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨(G.mem_neighborFinset z.1 u₁).mpr
            (by rw [huu]; exact (crossCommonNeighbor_spec G hfree hcf z y₂).1),
          (ConnectedComponent.mem_supp_iff a u₁).mp hu₁mem⟩
      · rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨(G.mem_neighborFinset x.1 u₁).mpr
            (crossCommonNeighbor_spec G hfree hcf x y₁).1,
          (ConnectedComponent.mem_supp_iff a u₁).mp hu₁mem⟩
    have hac' := (componentOwnerGraph_adj_iff_owner_eq_of_adj
      G hfree c hCxz a).mp hAxz
    exact hac hac'
  have hsameColorB : v₁ ≠ v₂ := by
    intro hvv
    have hBxz : (componentOwnerGraph G D b).Adj z.1 x.1 := by
      rw [componentOwnerGraph_adj]
      refine ⟨fun h => (componentOwnerGraph_adj G D c z.1 x.1).mp hCxz |>.1 h, ?_⟩
      refine ⟨v₁, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
      · rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨(G.mem_neighborFinset z.1 v₁).mpr
            (crossCommonNeighbor_spec G hfree hcf z y₁).1,
          (ConnectedComponent.mem_supp_iff b v₁).mp hv₁mem⟩
      · rw [componentNeighborFinset, Finset.mem_filter]
        exact ⟨(G.mem_neighborFinset x.1 v₁).mpr
            (by rw [hvv]; exact (crossCommonNeighbor_spec G hfree hcf x y₂).1),
          (ConnectedComponent.mem_supp_iff b v₁).mp hv₁mem⟩
    have hbc' := (componentOwnerGraph_adj_iff_owner_eq_of_adj
      G hfree c hCxz b).mp hBxz
    exact hbc hbc'
  have hcross (u : V) (hu : u ∈ a.supp) (v : V) (hv : v ∈ b.supp) : u ≠ v := by
    intro h
    have hua := (ConnectedComponent.mem_supp_iff a u).mp hu
    have hvb := (ConnectedComponent.mem_supp_iff b v).mp hv
    exact hab (hua.symm.trans ((congrArg D.connectedComponentMk h).trans hvb))
  exact ⟨hsameColorA, hsameColorB,
    hcross u₁ hu₁mem v₁ hv₁mem,
    hcross u₁ hu₁mem v₂ hv₂mem,
    hcross u₂ hu₂mem v₁ hv₁mem,
    hcross u₂ hu₂mem v₂ hv₂mem⟩

/-- Graph-facing adapter from the unordered-collision bowtie to its four
vertices and canonical-center separation package. -/
theorem hasOppositeThirdEdgeInBlock_canonicalCenter_separation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {c f a b : (secondOrderDefectGraph G).ConnectedComponent}
    (hcf : c ≠ f) (hac : a ≠ c) (hbc : b ≠ c) (hab : a ≠ b)
    (hopp : HasOppositeThirdEdgeInBlock (secondOrderDefectGraph G)
      (componentOwnerGraph G (secondOrderDefectGraph G) a)
      (componentOwnerGraph G (secondOrderDefectGraph G) b)
      (componentOwnerGraph G (secondOrderDefectGraph G) c) c f) :
    ∃ x z : c.supp, ∃ y₁ y₂ : f.supp,
      y₁.1 ≠ y₂.1 ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj x.1 y₁.1 ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y₁.1 z.1 ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj z.1 y₂.1 ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj y₂.1 x.1 ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj z.1 x.1 ∧
      (let u₁ := crossCommonNeighbor G hfree hcf x y₁
       let v₁ := crossCommonNeighbor G hfree hcf z y₁
       let u₂ := crossCommonNeighbor G hfree hcf z y₂
       let v₂ := crossCommonNeighbor G hfree hcf x y₂
       u₁ ≠ u₂ ∧ v₁ ≠ v₂ ∧
         u₁ ≠ v₁ ∧ u₁ ≠ v₂ ∧ u₂ ≠ v₁ ∧ u₂ ≠ v₂) := by
  classical
  obtain ⟨p, hp, r, hr, hzx, hxz, hy⟩ :=
    oppositeThirdEdge_closings_ne_of_distinct_owners
      G hfree a b c c f hab hopp
  have hpData := Finset.mem_filter.mp hp
  have hrData := Finset.mem_filter.mp hr
  have hpColor := (Finset.mem_filter.mp hpData.1).2
  have hrColor := (Finset.mem_filter.mp hrData.1).2
  let x : c.supp := ⟨p.1, hpData.2.1⟩
  let z : c.supp := ⟨p.2.1, hpData.2.2.2⟩
  let y₁ : f.supp := ⟨p.2.2, hpData.2.2.1⟩
  let y₂ : f.supp := ⟨r.2.2, hrData.2.2.1⟩
  have hAxy₁ : (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj
      x.1 y₁.1 := hpColor.1
  have hBy₁z : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj
      y₁.1 z.1 := hpColor.2.1
  have hAzy₂ : (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj
      z.1 y₂.1 := by
    change (componentOwnerGraph G (secondOrderDefectGraph G) a).Adj p.2.1 r.2.2
    rw [hzx]
    exact hrColor.1
  have hBy₂x : (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj
      y₂.1 x.1 := by
    change (componentOwnerGraph G (secondOrderDefectGraph G) b).Adj r.2.2 p.1
    rw [hxz]
    exact hrColor.2.1
  have hCxz : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj
      z.1 x.1 := hpColor.2.2
  have hsep := oppositeOwnerBowtie_canonicalCenter_separation
    G hfree hcf hac hbc hab x z y₁ y₂
      hAxy₁ hBy₁z hAzy₂ hBy₂x hCxz
  exact ⟨x, z, y₁, y₂, hy, hAxy₁, hBy₁z, hAzy₂, hBy₂x, hCxz, hsep⟩

end

end Erdos85

#print axioms Erdos85.crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
#print axioms Erdos85.oppositeOwnerBowtie_canonicalCenter_separation
#print axioms Erdos85.hasOppositeThirdEdgeInBlock_canonicalCenter_separation
