import Proofs.Erdos85BinarySquareRoutingStarCompletions

/-! # Excess routing lifts force an owner-factor rainbow triangle -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The two shared-center completions exhaust the non-rainbow routing lifts.
Thus a third monochromatic lift forces a triangle whose three edges have the
three endpoint owner colors. -/
theorem binarySquare_regular_sizeTwoRoutingColor_rainbow_of_three_le_lift_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    {c e f d : (secondOrderDefectGraph G).ConnectedComponent}
    (hce : c ≠ e) (hef : e ≠ f) (hcf : c ≠ f)
    (he : e.supp.ncard = q * 2)
    (x : c.supp) (w : f.supp)
    (hdirect : crossIntermediateComponent G hfree hcf x w = d)
    (hthree : 3 ≤ ((Finset.univ : Finset e.supp).filter fun z =>
      crossIntermediateComponent G hfree hce x z = d ∧
        crossIntermediateComponent G hfree hef z w = d).card) :
    ∃ y₁ y₂ y₃ : d.supp,
      y₁ ≠ y₂ ∧ y₂ ≠ y₃ ∧ y₃ ≠ y₁ ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) e).Adj y₁.1 y₂.1 ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) f).Adj y₂.1 y₃.1 ∧
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj y₃.1 y₁.1 := by
  classical
  let L := (Finset.univ : Finset e.supp).filter fun z =>
    crossIntermediateComponent G hfree hce x z = d ∧
      crossIntermediateComponent G hfree hef z w = d
  have hLcard : 3 ≤ L.card := by simpa [L] using hthree
  let y₀ := crossCommonNeighbor G hfree hcf x w
  have hy₀mem : y₀ ∈ d.supp := by
    rw [← hdirect]
    exact crossCommonNeighbor_mem_intermediate G hfree hcf x w
  let y : d.supp := ⟨y₀, hy₀mem⟩
  let S := componentCrossNeighborFinset G e y
  have hScard : S.card = 2 := by
    rw [show S = componentCrossNeighborFinset G e y by rfl,
      card_componentCrossNeighborFinset_eq_componentNeighborFinset]
    exact binarySquare_regular_sizeTwoPart_selector_card
      G hfree hq hreg hcard e he y.1
  have hexcess : ∃ z, z ∈ L ∧ z ∉ S := by
    by_contra h
    push Not at h
    have hLsubS : L ⊆ S := by
      intro z hz
      exact h z hz
    have hle := Finset.card_le_card hLsubS
    omega
  obtain ⟨z, hzL, hzS⟩ := hexcess
  have hzroute :
      crossIntermediateComponent G hfree hce x z = d ∧
        crossIntermediateComponent G hfree hef z w = d := by
    simpa [L] using hzL
  obtain ⟨y₁, y₂, y₃, hxy₁, hzy₁, hzy₂, hwy₂, hxy₃, hwy₃,
      hy₁comp, hy₂comp, hy₃comp, hshape⟩ :=
    monochromatic_routing_triangle_commonNeighbor_dichotomy
      G hfree hce hef hcf x z w hzroute.1 hzroute.2 hdirect
  have hrainbow :
      y₁ ≠ y₂ ∧ y₂ ≠ y₃ ∧ y₃ ≠ y₁ ∧
        (componentOwnerGraph G (secondOrderDefectGraph G) e).Adj y₁ y₂ ∧
        (componentOwnerGraph G (secondOrderDefectGraph G) f).Adj y₂ y₃ ∧
        (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj y₃ y₁ := by
    rcases hshape with hshared | hrainbow
    · have hy₃eq : y₃ = y.1 := by
        exact eq_crossCommonNeighbor_of_adj G hfree hcf x w
          ⟨hxy₃, hwy₃⟩
      have hzMemS : z ∈ S := by
        change z ∈ componentCrossNeighborFinset G e y
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ z, ?_⟩
        rw [← hy₃eq, ← hshared.2]
        exact hzy₂.symm
      exact False.elim (hzS hzMemS)
    · exact hrainbow
  have hy₁mem : y₁ ∈ d.supp :=
    (ConnectedComponent.mem_supp_iff d y₁).mpr hy₁comp
  have hy₂mem : y₂ ∈ d.supp :=
    (ConnectedComponent.mem_supp_iff d y₂).mpr hy₂comp
  have hy₃mem : y₃ ∈ d.supp :=
    (ConnectedComponent.mem_supp_iff d y₃).mpr hy₃comp
  refine ⟨⟨y₁, hy₁mem⟩, ⟨y₂, hy₂mem⟩, ⟨y₃, hy₃mem⟩, ?_, ?_, ?_,
    hrainbow.2.2.2.1, hrainbow.2.2.2.2.1, hrainbow.2.2.2.2.2⟩
  · intro h
    exact hrainbow.1 (congrArg Subtype.val h)
  · intro h
    exact hrainbow.2.1 (congrArg Subtype.val h)
  · intro h
    exact hrainbow.2.2.1 (congrArg Subtype.val h)

end

end Erdos85
