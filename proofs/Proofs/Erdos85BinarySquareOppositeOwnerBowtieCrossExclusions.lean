import Proofs.Erdos85BinarySquareOppositeOwnerBowtieCenters

/-! # Opposite-root exclusions in an opposite-owner bowtie -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A common neighbor lying in the wrong owner component cannot also meet the
other endpoint of an already-owned pair. -/
theorem commonNeighbor_mem_distinct_owner_not_adj_otherEndpoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {edgeOwner owner : (secondOrderDefectGraph G).ConnectedComponent}
    (hne : owner ≠ edgeOwner) {x z u : V}
    (hEdge : (componentOwnerGraph G (secondOrderDefectGraph G) edgeOwner).Adj x z)
    (hu : u ∈ owner.supp) (hxu : G.Adj x u) :
    ¬ G.Adj z u := by
  intro hzu
  have hOwner : (componentOwnerGraph G (secondOrderDefectGraph G) owner).Adj x z := by
    rw [componentOwnerGraph_adj]
    refine ⟨(componentOwnerGraph_adj G (secondOrderDefectGraph G)
      edgeOwner x z).mp hEdge |>.1, ?_⟩
    refine ⟨u, Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset x u).mpr hxu,
        (ConnectedComponent.mem_supp_iff owner u).mp hu⟩
    · rw [componentNeighborFinset, Finset.mem_filter]
      exact ⟨(G.mem_neighborFinset z u).mpr hzu,
        (ConnectedComponent.mem_supp_iff owner u).mp hu⟩
  have heq := (componentOwnerGraph_adj_iff_owner_eq_of_adj
    G hfree edgeOwner hEdge owner).mp hOwner
  exact hne heq

/-- Each of the four canonical bowtie centers avoids the opposite root of the
internal edge.  These are the four length-two chords which would give that
edge a second owner. -/
theorem oppositeOwnerBowtie_canonicalCenter_oppositeRoot_exclusions
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {c f a b : (secondOrderDefectGraph G).ConnectedComponent}
    (hcf : c ≠ f) (hac : a ≠ c) (hbc : b ≠ c)
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
    ¬ G.Adj z.1 u₁ ∧ ¬ G.Adj x.1 v₁ ∧
      ¬ G.Adj x.1 u₂ ∧ ¬ G.Adj z.1 v₂ := by
  let u₁ := crossCommonNeighbor G hfree hcf x y₁
  let v₁ := crossCommonNeighbor G hfree hcf z y₁
  let u₂ := crossCommonNeighbor G hfree hcf z y₂
  let v₂ := crossCommonNeighbor G hfree hcf x y₂
  have hu₁mem : u₁ ∈ a.supp :=
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
      G hfree hcf x y₁ hAxy₁
  have hv₁mem : v₁ ∈ b.supp :=
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj G hfree hcf z y₁
      (by exact ((componentOwnerGraph G (secondOrderDefectGraph G) b).adj_comm
        z.1 y₁.1).mpr hBy₁z)
  have hu₂mem : u₂ ∈ a.supp :=
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj
      G hfree hcf z y₂ hAzy₂
  have hv₂mem : v₂ ∈ b.supp :=
    crossCommonNeighbor_mem_owner_of_componentOwnerGraph_adj G hfree hcf x y₂
      (by exact ((componentOwnerGraph G (secondOrderDefectGraph G) b).adj_comm
        x.1 y₂.1).mpr hBy₂x)
  have hxu₁ := (crossCommonNeighbor_spec G hfree hcf x y₁).1
  have hzv₁ := (crossCommonNeighbor_spec G hfree hcf z y₁).1
  have hzu₂ := (crossCommonNeighbor_spec G hfree hcf z y₂).1
  have hxv₂ := (crossCommonNeighbor_spec G hfree hcf x y₂).1
  have hCzx : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x.1 z.1 :=
    ((componentOwnerGraph G (secondOrderDefectGraph G) c).adj_comm x.1 z.1).mpr hCxz
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact commonNeighbor_mem_distinct_owner_not_adj_otherEndpoint
      G hfree hac hCzx hu₁mem hxu₁
  · exact commonNeighbor_mem_distinct_owner_not_adj_otherEndpoint
      G hfree hbc hCxz hv₁mem hzv₁
  · exact commonNeighbor_mem_distinct_owner_not_adj_otherEndpoint
      G hfree hac hCxz hu₂mem hzu₂
  · exact commonNeighbor_mem_distinct_owner_not_adj_otherEndpoint
      G hfree hbc hCzx hv₂mem hxv₂

/-- Complete graph-facing routing skeleton supplied by the opposite
orientation branch: four alternating owner edges, four pairwise-distinct
canonical centers, and all four opposite-root chords absent. -/
theorem hasOppositeThirdEdgeInBlock_routingSkeleton
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
       (u₁ ≠ u₂ ∧ v₁ ≠ v₂ ∧
          u₁ ≠ v₁ ∧ u₁ ≠ v₂ ∧ u₂ ≠ v₁ ∧ u₂ ≠ v₂) ∧
       (¬ G.Adj z.1 u₁ ∧ ¬ G.Adj x.1 v₁ ∧
          ¬ G.Adj x.1 u₂ ∧ ¬ G.Adj z.1 v₂)) := by
  obtain ⟨x, z, y₁, y₂, hy, hAxy₁, hBy₁z, hAzy₂, hBy₂x, hCxz, hsep⟩ :=
    hasOppositeThirdEdgeInBlock_canonicalCenter_separation
      G hfree hcf hac hbc hab hopp
  have hexcl := oppositeOwnerBowtie_canonicalCenter_oppositeRoot_exclusions
    G hfree hcf hac hbc x z y₁ y₂ hAxy₁ hBy₁z hAzy₂ hBy₂x hCxz
  exact ⟨x, z, y₁, y₂, hy, hAxy₁, hBy₁z, hAzy₂, hBy₂x, hCxz,
    hsep, hexcl⟩

end

end Erdos85

#print axioms Erdos85.commonNeighbor_mem_distinct_owner_not_adj_otherEndpoint
#print axioms Erdos85.oppositeOwnerBowtie_canonicalCenter_oppositeRoot_exclusions
#print axioms Erdos85.hasOppositeThirdEdgeInBlock_routingSkeleton
