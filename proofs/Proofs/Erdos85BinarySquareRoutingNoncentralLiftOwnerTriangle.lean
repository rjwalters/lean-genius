import Proofs.Erdos85BinarySquareRoutingTriangleLift
import Proofs.Erdos85BinarySquareFourSelectorUniqueLabel

/-! # Noncentral routing lifts force owner triangles -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A monochromatic lift which does not pass through the direct endpoint
pair's chosen common center must lie in the distinct-center branch.  Hence it
forces a rainbow triangle in the three owner colors. -/
theorem noncentral_monochromatic_routing_lift_exists_rainbow_ownerTriangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    {c e f : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f)
    (x : c.supp) (z : e.supp) (w : f.supp)
    (hxz : crossIntermediateComponent G hfree hce x z =
      crossIntermediateComponent G hfree hcf x w)
    (hzw : crossIntermediateComponent G hfree hef z w =
      crossIntermediateComponent G hfree hcf x w)
    (hnoncentral : ¬ G.Adj z.1 (crossCommonNeighbor G hfree hcf x w)) :
    ∃ y₁ y₂ y₃ : V,
      y₁ ≠ y₂ ∧ y₂ ≠ y₃ ∧ y₃ ≠ y₁ ∧
      (secondOrderDefectGraph G).connectedComponentMk y₁ =
        crossIntermediateComponent G hfree hcf x w ∧
      (secondOrderDefectGraph G).connectedComponentMk y₂ =
        crossIntermediateComponent G hfree hcf x w ∧
      (secondOrderDefectGraph G).connectedComponentMk y₃ =
        crossIntermediateComponent G hfree hcf x w ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) e).Adj y₁ y₂ ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) f).Adj y₂ y₃ ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj y₃ y₁ := by
  let d := crossIntermediateComponent G hfree hcf x w
  obtain ⟨y₁, y₂, y₃, hxy₁, hzy₁, hzy₂, hwy₂, hxy₃, hwy₃,
      hy₁comp, hy₂comp, hy₃comp, hcases⟩ :=
    monochromatic_routing_triangle_commonNeighbor_dichotomy
      G hfree hce hef hcf x z w hxz hzw rfl
  rcases hcases with hshared | hrainbow
  · exfalso
    rcases hshared with ⟨hy₁₂, hy₂₃⟩
    apply hnoncentral
    have hy₃eq : y₃ = crossCommonNeighbor G hfree hcf x w :=
      eq_crossCommonNeighbor_of_adj G hfree hcf x w ⟨hxy₃, hwy₃⟩
    rw [← hy₃eq, ← hy₂₃]
    exact hzy₂
  · rcases hrainbow with
      ⟨hy₁₂, hy₂₃, hy₃₁, hownerE, hownerF, hownerC⟩
    exact ⟨y₁, y₂, y₃, hy₁₂, hy₂₃, hy₃₁,
      hy₁comp, hy₂comp, hy₃comp, hownerE, hownerF, hownerC⟩

/-- A third same-color lift is necessarily noncentral, because the selector
of the direct common center has exactly two points in a normalized size-two
intermediate coordinate. Thus lift multiplicity at least three forces the
rainbow owner triangle. -/
theorem three_le_monochromatic_routing_lift_card_exists_rainbow_ownerTriangle
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q) (hcard : Fintype.card V = q * q)
    {c e f : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f)
    (he : e.supp.ncard = q * 2)
    (x : c.supp) (w : f.supp)
    (hthree : 3 ≤ ((Finset.univ : Finset e.supp).filter fun z =>
      crossIntermediateComponent G hfree hcf x w =
          crossIntermediateComponent G hfree hce x z ∧
        crossIntermediateComponent G hfree hcf x w =
          crossIntermediateComponent G hfree hef z w).card) :
    ∃ y₁ y₂ y₃ : V,
      y₁ ≠ y₂ ∧ y₂ ≠ y₃ ∧ y₃ ≠ y₁ ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) e).Adj y₁ y₂ ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) f).Adj y₂ y₃ ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj y₃ y₁ := by
  let y := crossCommonNeighbor G hfree hcf x w
  let L := (Finset.univ : Finset e.supp).filter fun z =>
    crossIntermediateComponent G hfree hcf x w =
        crossIntermediateComponent G hfree hce x z ∧
      crossIntermediateComponent G hfree hcf x w =
        crossIntermediateComponent G hfree hef z w
  let C := componentNeighborSupportFinset G e y
  have hCcard : C.card = 2 := by
    exact binarySquare_regular_componentNeighborSupportFinset_card_two
      G hfree hq hreg hcard e he y
  have hnsub : ¬L ⊆ C := by
    intro hsub
    have hle := Finset.card_le_card hsub
    change 3 ≤ L.card at hthree
    rw [hCcard] at hle
    omega
  obtain ⟨z, hzL, hzC⟩ := Finset.not_subset.mp hnsub
  have hzdata := (Finset.mem_filter.mp hzL).2
  have hnoncentral : ¬G.Adj z.1 y := by
    intro hzy
    apply hzC
    simp only [C, componentNeighborSupportFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [componentNeighborFinset, Finset.mem_filter]
    exact ⟨(G.mem_neighborFinset y z.1).mpr hzy.symm,
      (ConnectedComponent.mem_supp_iff e z.1).mp z.2⟩
  obtain ⟨y₁, y₂, y₃, h12, h23, h31, _hc1, _hc2, _hc3,
      hoE, hoF, hoC⟩ :=
    noncentral_monochromatic_routing_lift_exists_rainbow_ownerTriangle
      G hfree hce hef hcf x z w hzdata.1.symm hzdata.2.symm hnoncentral
  exact ⟨y₁, y₂, y₃, h12, h23, h31, hoE, hoF, hoC⟩

end

end Erdos85
