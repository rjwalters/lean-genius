import Proofs.Erdos85OrderSixtyFourOrthogonalArrayMatching

/-! # The balanced H16 restriction of the order-64 orthogonal array -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Restricting the six-column order-64 orthogonal array to H16 gives a
six-column, sixteen-row array in which every symbol occurs exactly twice
in every column. -/
theorem orderSixtyFour_seven_defect_components_orthogonalArray_H_restriction
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
          (∀ i j, i ≠ j →
            Function.Bijective (fun z : Fin 64 => (ℓ i z, ℓ j z))) ∧
          (∀ i (x : (κ i).1.supp) z, G.Adj x.1 z ↔ ℓ i z = x) ∧
          ∀ i (x : (κ i).1.supp),
            ((Finset.univ : Finset c.supp).filter
              (fun u => ℓ i u.1 = x)).card = 2 := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, κ, ℓ, hpair, hiff, _hdiag⟩ :=
    orderSixtyFour_seven_defect_components_orthogonalArray_matching
      G hfree hmin hcover hcount
  obtain ⟨c', hc'16, htwo', hsmall'⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  have hcc' : c = c' := by
    by_contra hne
    have hc8 := (hsmall' c hne).1
    omega
  have htwo (z : Fin 64) :
      (componentNeighborFinset G D c z).card = 2 := by
    rw [hcc']
    exact htwo' z
  refine ⟨c, hc16, κ, ℓ, hpair, hiff, ?_⟩
  intro i x
  let S : Finset c.supp :=
    (Finset.univ : Finset c.supp).filter (fun u => ℓ i u.1 = x)
  let ι : c.supp ↪ Fin 64 :=
    .subtype (fun z : Fin 64 => z ∈ c.supp)
  have hmap : S.map ι = componentNeighborFinset G D c x.1 := by
    ext z
    constructor
    · intro hz
      obtain ⟨u, hu, huz⟩ := Finset.mem_map.mp hz
      have huLabel : ℓ i u.1 = x :=
        (Finset.mem_filter.mp hu).2
      subst z
      apply Finset.mem_filter.mpr
      refine ⟨(G.mem_neighborFinset x.1 u.1).mpr
        ((hiff i x u.1).mpr huLabel), ?_⟩
      exact (ConnectedComponent.mem_supp_iff c u.1).mp u.2
    · intro hz
      have hz' := Finset.mem_filter.mp hz
      have hxz : G.Adj x.1 z :=
        (G.mem_neighborFinset x.1 z).mp hz'.1
      have hzc := hz'.2
      let u : c.supp :=
        ⟨z, (ConnectedComponent.mem_supp_iff c z).mpr hzc⟩
      apply Finset.mem_map.mpr
      refine ⟨u, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (hiff i x z).mp hxz⟩
  change S.card = 2
  rw [← Finset.card_map ι, hmap, htwo]

end

end Erdos85
