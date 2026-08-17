import Proofs.Erdos85BinarySquareRestrictedOwnerResolution
import Proofs.Erdos85BinarySquareMixedOwnerTriangleCensus

/-! # Exact owner-color partition of component-complement triangles -/

open SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000 in

/-- Every ordered triangle in the complement of a defect component has a
unique ordered triple of restricted owner colors.  Thus the restricted-owner
colored triangle finsets form an exact partition of the ambient complement
triangle finset. -/
theorem mem_componentComplement_cyclicTriples_iff_existsUnique_ownerColors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (d : (secondOrderDefectGraph G).ConnectedComponent)
    (p : d.supp × d.supp × d.supp) :
    p ∈ cyclicColoredTriples
        ((secondOrderDefectGraph G).induce d.supp)ᶜ
        ((secondOrderDefectGraph G).induce d.supp)ᶜ
        ((secondOrderDefectGraph G).induce d.supp)ᶜ ↔
      ∃! colors :
          (secondOrderDefectGraph G).ConnectedComponent ×
            (secondOrderDefectGraph G).ConnectedComponent ×
            (secondOrderDefectGraph G).ConnectedComponent,
        p ∈ cyclicColoredTriples
          (restrictedComponentOwnerGraph G d colors.1)
          (restrictedComponentOwnerGraph G d colors.2.2)
          (restrictedComponentOwnerGraph G d colors.2.1) := by
  classical
  simp only [cyclicColoredTriples, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hxy, hyz, hzx⟩
    obtain ⟨a, ha, hua⟩ :=
      (inducedDefectComponent_compl_adj_iff_existsUnique_restrictedOwner_adj
        G hfree d p.1 p.2.2).mp hxy
    obtain ⟨b, hb, hub⟩ :=
      (inducedDefectComponent_compl_adj_iff_existsUnique_restrictedOwner_adj
        G hfree d p.2.2 p.2.1).mp hyz
    obtain ⟨c, hc, huc⟩ :=
      (inducedDefectComponent_compl_adj_iff_existsUnique_restrictedOwner_adj
        G hfree d p.2.1 p.1).mp hzx
    refine ⟨(a, c, b), ⟨ha, hb, hc⟩, ?_⟩
    rintro ⟨a', c', b'⟩ ⟨ha', hb', hc'⟩
    have hA : a' = a := hua a' ha'
    have hB : b' = b := hub b' hb'
    have hC : c' = c := huc c' hc'
    subst a'
    subst b'
    subst c'
    rfl
  · rintro ⟨⟨a, c, b⟩, ⟨ha, hb, hc⟩, huniq⟩
    exact ⟨
      (inducedDefectComponent_compl_adj_iff_existsUnique_restrictedOwner_adj
        G hfree d p.1 p.2.2).mpr
          ⟨a, ha, fun a' ha' =>
            restrictedOwner_adj_color_unique G hfree
              (d := d) (a := a) (b := a') (x := p.1) (y := p.2.2) ha ha' |>.symm⟩,
      (inducedDefectComponent_compl_adj_iff_existsUnique_restrictedOwner_adj
        G hfree d p.2.2 p.2.1).mpr
          ⟨b, hb, fun b' hb' =>
            restrictedOwner_adj_color_unique G hfree
              (d := d) (a := b) (b := b') (x := p.2.2) (y := p.2.1) hb hb' |>.symm⟩,
      (inducedDefectComponent_compl_adj_iff_existsUnique_restrictedOwner_adj
        G hfree d p.2.1 p.1).mpr
          ⟨c, hc, fun c' hc' =>
            restrictedOwner_adj_color_unique G hfree
              (d := d) (a := c) (b := c') (x := p.2.1) (y := p.1) hc hc' |>.symm⟩⟩

end

end Erdos85
