import Proofs.Erdos85BinarySquareRestrictedOwnerResolution
import Proofs.Erdos85BinarySquareMixedOwnerTriangleCensus
import Proofs.Erdos85OrderSixtyFourDefectComplementTriangleLedger

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

/-- Cardinal form of the exact partition: the ambient ordered complement
triangle census is the sum of all its ordered restricted-owner color fibers. -/
theorem sum_card_restrictedOwner_cyclicTriples_eq_componentComplement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G)
    (d : (secondOrderDefectGraph G).ConnectedComponent) :
    (∑ colors :
        (secondOrderDefectGraph G).ConnectedComponent ×
          (secondOrderDefectGraph G).ConnectedComponent ×
          (secondOrderDefectGraph G).ConnectedComponent,
      (cyclicColoredTriples
        (restrictedComponentOwnerGraph G d colors.1)
        (restrictedComponentOwnerGraph G d colors.2.2)
        (restrictedComponentOwnerGraph G d colors.2.1)).card) =
      (cyclicColoredTriples
        ((secondOrderDefectGraph G).induce d.supp)ᶜ
        ((secondOrderDefectGraph G).induce d.supp)ᶜ
        ((secondOrderDefectGraph G).induce d.supp)ᶜ).card := by
  classical
  rw [← Finset.card_sigma]
  apply Finset.card_bij (fun q _ => q.2)
  · intro q hq
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hq
    have hcolors : ∃! colors :
        (secondOrderDefectGraph G).ConnectedComponent ×
          (secondOrderDefectGraph G).ConnectedComponent ×
          (secondOrderDefectGraph G).ConnectedComponent,
        q.2 ∈ cyclicColoredTriples
          (restrictedComponentOwnerGraph G d colors.1)
          (restrictedComponentOwnerGraph G d colors.2.2)
          (restrictedComponentOwnerGraph G d colors.2.1) := by
      refine ⟨q.1, hq, ?_⟩
      intro colors habc
      simp only [cyclicColoredTriples, Finset.mem_filter,
        Finset.mem_univ, true_and] at hq habc
      apply Prod.ext
      · exact restrictedOwner_adj_color_unique G hfree habc.1 hq.1
      · apply Prod.ext
        · exact restrictedOwner_adj_color_unique G hfree habc.2.2 hq.2.2
        · exact restrictedOwner_adj_color_unique G hfree habc.2.1 hq.2.1
    exact (mem_componentComplement_cyclicTriples_iff_existsUnique_ownerColors
      G hfree d q.2).mpr hcolors
  · intro q hq r hr hqr
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hq hr
    have hcomp := (mem_componentComplement_cyclicTriples_iff_existsUnique_ownerColors
      G hfree d q.2).mpr (by
        refine ⟨q.1, hq, ?_⟩
        intro colors hcolors
        simp only [cyclicColoredTriples, Finset.mem_filter,
          Finset.mem_univ, true_and] at hq hcolors
        apply Prod.ext
        · exact restrictedOwner_adj_color_unique G hfree hcolors.1 hq.1
        · apply Prod.ext
          · exact restrictedOwner_adj_color_unique G hfree hcolors.2.2 hq.2.2
          · exact restrictedOwner_adj_color_unique G hfree hcolors.2.1 hq.2.1)
    obtain ⟨colors, hcolors, huniq⟩ :=
      (mem_componentComplement_cyclicTriples_iff_existsUnique_ownerColors
        G hfree d q.2).mp hcomp
    have hqcolors : q.1 = colors := huniq q.1 hq
    have hr' : r.2 ∈ cyclicColoredTriples
          (restrictedComponentOwnerGraph G d r.1.1)
          (restrictedComponentOwnerGraph G d r.1.2.2)
          (restrictedComponentOwnerGraph G d r.1.2.1) := hr
    rw [← hqr] at hr'
    have hrcolors : r.1 = colors := huniq r.1 hr'
    have hqrColors : q.1 = r.1 := hqcolors.trans hrcolors.symm
    cases q with
    | mk qColors qp =>
      cases r with
      | mk rColors rp =>
        simp only at hqr hqrColors
        subst rColors
        cases hqr
        rfl
  · intro p hp
    obtain ⟨colors, hcolors, huniq⟩ :=
      (mem_componentComplement_cyclicTriples_iff_existsUnique_ownerColors
        G hfree d p).mp hp
    refine ⟨⟨colors, p⟩, ?_, rfl⟩
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and]
    exact hcolors

/-- In the order-64 four-component branch, the sum of all ordered restricted
owner-color triangle fibers inside one defect component is at most `672`.
This is the oriented form of the complement's `112`-triangle budget. -/
theorem orderSixtyFour_sum_card_restrictedOwner_cyclicTriples_le_672
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    (d : (secondOrderDefectGraph G).ConnectedComponent) :
    (∑ colors :
        (secondOrderDefectGraph G).ConnectedComponent ×
          (secondOrderDefectGraph G).ConnectedComponent ×
          (secondOrderDefectGraph G).ConnectedComponent,
      (cyclicColoredTriples
        (restrictedComponentOwnerGraph G d colors.1)
        (restrictedComponentOwnerGraph G d colors.2.2)
        (restrictedComponentOwnerGraph G d colors.2.1)).card) ≤ 672 := by
  classical
  let H := (secondOrderDefectGraph G).induce d.supp
  rw [sum_card_restrictedOwner_cyclicTriples_eq_componentComplement G hfree d]
  change (cyclicColoredTriples Hᶜ Hᶜ Hᶜ).card ≤ 672
  have hd := orderSixtyFour_regular_four_defectComponents_all_orderSixteen
    G hfree hreg hcount d
  have hcardH : Fintype.card d.supp = 16 := by
    rw [show Fintype.card d.supp = d.supp.ncard by
      simpa [Nat.card_eq_fintype_card] using Nat.card_coe_set_eq d.supp]
    exact hd
  have htraceCard := trace_three_adjMatrices_eq_card_cyclicColoredTriples
    Hᶜ Hᶜ Hᶜ
  have htraceTriangle :=
    trace_adjMatrix_cube_eq_six_mul_triangleMinorCount Hᶜ (by omega)
  have hcard : (cyclicColoredTriples Hᶜ Hᶜ Hᶜ).card =
      6 * (adjacencyTriangleMinorFinset Hᶜ).card := by
    rw [htraceTriangle] at htraceCard
    norm_cast at htraceCard
    omega
  rw [hcard]
  have hminor := orderSixtyFour_defectComponent_compl_triangleMinorCount_le
    G hfree hreg hcount d
  change (adjacencyTriangleMinorFinset Hᶜ).card ≤ 112 at hminor
  omega

end

end Erdos85
