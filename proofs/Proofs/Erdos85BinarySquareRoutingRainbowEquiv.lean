import Proofs.Erdos85BinarySquareRoutingRainbowRealization

/-! # Exact equivalence between routing rainbows and owner rainbows -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Ordered owner-colored rainbow triangles inside routing component `d`. -/
def ownerRainbowTriples
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (d e f c : (secondOrderDefectGraph G).ConnectedComponent) :=
  {p : d.supp × (d.supp × d.supp) //
    p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2 ∧ p.2.2 ≠ p.1 ∧
    (componentOwnerGraph G (secondOrderDefectGraph G) e).Adj p.1.1 p.2.1.1 ∧
    (componentOwnerGraph G (secondOrderDefectGraph G) f).Adj p.2.1.1 p.2.2.1 ∧
    (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj p.2.2.1 p.1.1}

/-- Ordered endpoint triples whose three routes equal `d` and whose canonical
pairwise common neighbors are pairwise distinct. -/
def routingRainbowEndpointTriples
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f) :=
  {p : c.supp × (e.supp × f.supp) //
    crossIntermediateComponent G hfree hce p.1 p.2.1 = d ∧
    crossIntermediateComponent G hfree hef p.2.1 p.2.2 = d ∧
    crossIntermediateComponent G hfree hcf p.1 p.2.2 = d ∧
    crossCommonNeighbor G hfree hce p.1 p.2.1 ≠
      crossCommonNeighbor G hfree hef p.2.1 p.2.2 ∧
    crossCommonNeighbor G hfree hef p.2.1 p.2.2 ≠
      crossCommonNeighbor G hfree hcf p.1 p.2.2 ∧
    crossCommonNeighbor G hfree hcf p.1 p.2.2 ≠
      crossCommonNeighbor G hfree hce p.1 p.2.1}

noncomputable instance ownerRainbowTriples.instFintype
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (d e f c : (secondOrderDefectGraph G).ConnectedComponent) :
    Fintype (ownerRainbowTriples G d e f c) := by
  classical
  unfold ownerRainbowTriples
  infer_instance

noncomputable instance routingRainbowEndpointTriples.instFintype
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f) :
    Fintype (routingRainbowEndpointTriples G hfree c d e f hce hef hcf) := by
  classical
  unfold routingRainbowEndpointTriples
  infer_instance

/-- Send a routing-rainbow endpoint triple to its three canonical centers. -/
def routingRainbowToOwner
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f) :
    routingRainbowEndpointTriples G hfree c d e f hce hef hcf →
      ownerRainbowTriples G d e f c := by
  rintro ⟨⟨x, z, w⟩, hr₁, hr₂, hr₃, h12, h23, h31⟩
  let y₁₀ := crossCommonNeighbor G hfree hce x z
  let y₂₀ := crossCommonNeighbor G hfree hef z w
  let y₃₀ := crossCommonNeighbor G hfree hcf x w
  have hy₁mem : y₁₀ ∈ d.supp := by
    rw [← hr₁]
    exact crossCommonNeighbor_mem_intermediate G hfree hce x z
  have hy₂mem : y₂₀ ∈ d.supp := by
    rw [← hr₂]
    exact crossCommonNeighbor_mem_intermediate G hfree hef z w
  have hy₃mem : y₃₀ ∈ d.supp := by
    rw [← hr₃]
    exact crossCommonNeighbor_mem_intermediate G hfree hcf x w
  let y₁ : d.supp := ⟨y₁₀, hy₁mem⟩
  let y₂ : d.supp := ⟨y₂₀, hy₂mem⟩
  let y₃ : d.supp := ⟨y₃₀, hy₃mem⟩
  have hcases := monochromatic_routing_completion_star_or_rainbow
    G hfree hce hef hcf x z w hr₁ hr₂ hr₃
  dsimp only at hcases
  have hnstar : ¬ (G.Adj z.1 y₃₀ ∧ y₁₀ = y₂₀ ∧ y₂₀ = y₃₀) := by
    intro hstar
    exact h12 hstar.2.1
  have hrainbow := hcases.resolve_left hnstar
  exact ⟨(y₁, (y₂, y₃)),
    (fun h => h12 (congrArg Subtype.val h)),
    (fun h => h23 (congrArg Subtype.val h)),
    (fun h => h31 (congrArg Subtype.val h)),
    hrainbow.2.2.2.1, hrainbow.2.2.2.2.1, hrainbow.2.2.2.2.2⟩

/-- Every owner rainbow is hit by the canonical-center map. -/
theorem routingRainbowToOwner_surjective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f) :
    Function.Surjective
      (routingRainbowToOwner G hfree c d e f hce hef hcf) := by
  rintro ⟨⟨y₁, y₂, y₃⟩, h12, h23, h31, hE, hF, hC⟩
  obtain ⟨x, z, w, hr₁, hr₂, hr₃, hy₁, hy₂, hy₃⟩ :=
    ownerRainbow_exists_monochromatic_routing_completion
      G hfree hce hef hcf y₁ y₂ y₃ hE hF hC
  let r : routingRainbowEndpointTriples G hfree c d e f hce hef hcf :=
    ⟨(x, (z, w)), hr₁, hr₂, hr₃,
      fun h => h12 (Subtype.ext (hy₁.symm.trans (h.trans hy₂))),
      fun h => h23 (Subtype.ext (hy₂.symm.trans (h.trans hy₃))),
      fun h => h31 (Subtype.ext (hy₃.symm.trans (h.trans hy₁)))⟩
  refine ⟨r, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact hy₁
  · apply Prod.ext
    · apply Subtype.ext
      exact hy₂
    · apply Subtype.ext
      exact hy₃

/-- Distinct routing endpoint triples have distinct canonical owner
rainbows. -/
theorem routingRainbowToOwner_injective
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f) :
    Function.Injective
      (routingRainbowToOwner G hfree c d e f hce hef hcf) := by
  intro r s hrs
  have hy₁ := congrArg (fun o : ownerRainbowTriples G d e f c => o.1.1.1) hrs
  have hy₂ := congrArg (fun o : ownerRainbowTriples G d e f c => o.1.2.1.1) hrs
  have hy₃ := congrArg (fun o : ownerRainbowTriples G d e f c => o.1.2.2.1) hrs
  rcases r with ⟨⟨x, z, w⟩, hr₁, hr₂, hr₃, h12, h23, h31⟩
  rcases s with ⟨⟨x', z', w'⟩, hs₁, hs₂, hs₃, hs12, hs23, hs31⟩
  change crossCommonNeighbor G hfree hce x z =
      crossCommonNeighbor G hfree hce x' z' at hy₁
  change crossCommonNeighbor G hfree hef z w =
      crossCommonNeighbor G hfree hef z' w' at hy₂
  change crossCommonNeighbor G hfree hcf x w =
      crossCommonNeighbor G hfree hcf x' w' at hy₃
  have unique_common {a b u v : V} (hab : a ≠ b)
      (hau : G.Adj a u) (hbu : G.Adj b u)
      (hav : G.Adj a v) (hbv : G.Adj b v) : u = v := by
    by_contra huv
    exact hfree (containsC4_of_rim hau hbu.symm hbv hav.symm hab huv
      (G.ne_of_adj hau).symm (G.ne_of_adj hbu).symm
      (G.ne_of_adj hav).symm (G.ne_of_adj hbv).symm)
  have hxz := crossCommonNeighbor_spec G hfree hce x z
  have hzw := crossCommonNeighbor_spec G hfree hef z w
  have hxw := crossCommonNeighbor_spec G hfree hcf x w
  have hxz' := crossCommonNeighbor_spec G hfree hce x' z'
  have hzw' := crossCommonNeighbor_spec G hfree hef z' w'
  have hxw' := crossCommonNeighbor_spec G hfree hcf x' w'
  rw [← hy₁] at hxz'
  rw [← hy₂] at hzw'
  rw [← hy₃] at hxw'
  have ex : x = x' := by
    apply Subtype.ext
    exact unique_common h31 hxw.1.symm hxz.1.symm hxw'.1.symm hxz'.1.symm
  have ez : z = z' := by
    apply Subtype.ext
    exact unique_common h12 hxz.2.symm hzw.1.symm hxz'.2.symm hzw'.1.symm
  have ew : w = w' := by
    apply Subtype.ext
    exact unique_common h23 hzw.2.symm hxw.2.symm hzw'.2.symm hxw'.2.symm
  apply Subtype.ext
  have ezw : (z, w) = (z', w') := Prod.ext ez ew
  exact Prod.ext ex ezw

/-- Routing-rainbow endpoint triples and owner-colored rainbow triangles have
exactly the same finite cardinality. -/
theorem routingRainbowEndpointTriples_card_eq_ownerRainbowTriples_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (c d e f : (secondOrderDefectGraph G).ConnectedComponent)
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f) :
    Fintype.card (routingRainbowEndpointTriples
      G hfree c d e f hce hef hcf) =
      Fintype.card (ownerRainbowTriples G d e f c) := by
  exact Fintype.card_congr (Equiv.ofBijective
    (routingRainbowToOwner G hfree c d e f hce hef hcf)
    ⟨routingRainbowToOwner_injective G hfree c d e f hce hef hcf,
      routingRainbowToOwner_surjective G hfree c d e f hce hef hcf⟩)

end

end Erdos85
