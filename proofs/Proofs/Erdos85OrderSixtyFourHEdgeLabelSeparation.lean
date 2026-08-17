import Proofs.Erdos85OrderSixtyFourOrthogonalArrayHRestriction
import Proofs.Erdos85OrderSixtyFourSixteenBlockCycles

/-! # No OA-label detour across an H16 edge -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- If two H16 vertices are adjacent, then no label neighbor of the first
is adjacent to a label neighbor of the second.  Such an edge would close a
four-cycle with the H16 edge. -/
theorem orderSixtyFour_seven_defect_components_H_edge_label_separation
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16 ∧
      ∃ κ : Fin 6 ≃ {k // k ≠ c},
        ∃ ℓ : ∀ i : Fin 6, Fin 64 → (κ i).1.supp,
          (∀ i (x : (κ i).1.supp) z, G.Adj x.1 z ↔ ℓ i z = x) ∧
          (∀ y : c.supp, (G.induce c.supp).degree y = 2) ∧
          (∀ (y u : c.supp), (G.induce c.supp).Adj y u →
            ∀ i j,
              (¬ G.Adj (ℓ i y.1).1 (ℓ j u.1).1) ∧
              ℓ i (ℓ j u.1).1 ≠ ℓ i y.1) ∧
          ∀ y : c.supp, 2 ≤
            ((Finset.univ : Finset c.supp).filter fun u =>
              ∀ i j, ℓ i (ℓ j u.1).1 ≠ ℓ i y.1).card := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, κ, ℓ, _hpair, hiff, _hbalance⟩ :=
    orderSixtyFour_seven_defect_components_orthogonalArray_H_restriction
      G hfree hmin hcover hcount
  obtain ⟨c', hc'16, hdeg'⟩ :=
    orderSixtyFour_seven_defect_components_sixteenBlock_twoRegular
      G hfree hmin hcover hcount
  obtain ⟨d, hd16, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  have hcd : c = d := by
    by_contra hne
    have hc8 := hsmall c hne
    omega
  subst d
  have hc' : c' = c := by
    by_contra hne
    have hc'8 := hsmall c' hne
    omega
  subst c'
  have hH_K (i : Fin 6) (y : c.supp) (x : (κ i).1.supp) :
      y.1 ≠ x.1 := by
    intro h
    have hycomp : D.connectedComponentMk y.1 = c :=
      (ConnectedComponent.mem_supp_iff c y.1).mp y.2
    have hxcomp : D.connectedComponentMk x.1 = (κ i).1 :=
      (ConnectedComponent.mem_supp_iff (κ i).1 x.1).mp x.2
    have hcEq : c = (κ i).1 :=
      hycomp.symm.trans ((congrArg D.connectedComponentMk h).trans hxcomp)
    exact (κ i).2 hcEq.symm
  have hedge : ∀ (y u : c.supp), (G.induce c.supp).Adj y u →
      ∀ i j,
        (¬ G.Adj (ℓ i y.1).1 (ℓ j u.1).1) ∧
        ℓ i (ℓ j u.1).1 ≠ ℓ i y.1 := by
    intro y u hyu i j
    let x : (κ i).1.supp := ℓ i y.1
    let x' : (κ j).1.supp := ℓ j u.1
    have hyx : G.Adj y.1 x.1 := ((hiff i x y.1).mpr rfl).symm
    have hx'u : G.Adj x'.1 u.1 := (hiff j x' u.1).mpr rfl
    have huy : u.1 ≠ y.1 := by
      intro h
      exact (G.induce c.supp).ne_of_adj hyu (Subtype.ext h.symm)
    have hnon : ¬ G.Adj x.1 x'.1 := by
      intro hcross
      have hxx' : x.1 ≠ x'.1 := G.ne_of_adj hcross
      exact hfree (containsC4_of_rim hyx hcross hx'u hyu.symm
        (hH_K j y x') ((hH_K i u x).symm) ((hH_K i y x).symm)
        hxx' huy (hH_K j u x'))
    refine ⟨hnon, ?_⟩
    intro heq
    apply hnon
    exact (hiff i x x'.1).mpr heq
  refine ⟨c, hc16, κ, ℓ, hiff, hdeg', hedge, ?_⟩
  intro y
  let A : Finset c.supp :=
    (Finset.univ : Finset c.supp).filter fun u =>
      ∀ i j, ℓ i (ℓ j u.1).1 ≠ ℓ i y.1
  have hsub : (G.induce c.supp).neighborFinset y ⊆ A := by
    intro u hu
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i j
    exact (hedge y u
      (((G.induce c.supp).mem_neighborFinset y u).mp hu) i j).2
  have hcard := Finset.card_le_card hsub
  change 2 ≤ A.card
  rw [(G.induce c.supp).card_neighborFinset_eq_degree, hdeg' y] at hcard
  exact hcard

end

end Erdos85
