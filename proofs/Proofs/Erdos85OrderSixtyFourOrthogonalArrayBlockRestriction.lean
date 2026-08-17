import Proofs.Erdos85OrderSixtyFourOrthogonalArrayHRestriction

/-! # The seven balanced row classes of the order-64 orthogonal array -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The OA rows split into H16, where each column symbol occurs twice, and
six K8 blocks, where every column restricts to a permutation of its eight
symbols. -/
theorem orderSixtyFour_seven_defect_components_orthogonalArray_block_restriction
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
          (∀ i (x : (κ i).1.supp),
            ((Finset.univ : Finset c.supp).filter
              (fun u => ℓ i u.1 = x)).card = 2) ∧
          ∀ k i (x : (κ i).1.supp),
            ((Finset.univ : Finset (κ k).1.supp).filter
              (fun u => ℓ i u.1 = x)).card = 1 := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, κ, ℓ, hpair, hiff, hHbalance⟩ :=
    orderSixtyFour_seven_defect_components_orthogonalArray_H_restriction
      G hfree hmin hcover hcount
  obtain ⟨c', hc'16, _htwo', hsmall'⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  have hcc' : c = c' := by
    by_contra hne
    have hc8 := (hsmall' c hne).1
    omega
  have hsmall (k : Fin 6) (z : Fin 64) :
      (componentNeighborFinset G D (κ k).1 z).card = 1 := by
    exact (hsmall' (κ k).1 (by simpa [hcc'] using (κ k).2)).2 z
  refine ⟨c, hc16, κ, ℓ, hpair, hiff, hHbalance, ?_⟩
  intro k i x
  let S : Finset (κ k).1.supp :=
    (Finset.univ : Finset (κ k).1.supp).filter
      (fun u => ℓ i u.1 = x)
  let ι : (κ k).1.supp ↪ Fin 64 :=
    .subtype (fun z : Fin 64 => z ∈ (κ k).1.supp)
  have hmap : S.map ι =
      componentNeighborFinset G D (κ k).1 x.1 := by
    ext z
    constructor
    · intro hz
      obtain ⟨u, hu, huz⟩ := Finset.mem_map.mp hz
      have huLabel : ℓ i u.1 = x := (Finset.mem_filter.mp hu).2
      subst z
      apply Finset.mem_filter.mpr
      refine ⟨(G.mem_neighborFinset x.1 u.1).mpr
        ((hiff i x u.1).mpr huLabel), ?_⟩
      exact (ConnectedComponent.mem_supp_iff (κ k).1 u.1).mp u.2
    · intro hz
      have hz' := Finset.mem_filter.mp hz
      have hxz : G.Adj x.1 z :=
        (G.mem_neighborFinset x.1 z).mp hz'.1
      let u : (κ k).1.supp :=
        ⟨z, (ConnectedComponent.mem_supp_iff (κ k).1 z).mpr hz'.2⟩
      apply Finset.mem_map.mpr
      refine ⟨u, ?_, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, (hiff i x z).mp hxz⟩
  change S.card = 1
  rw [← Finset.card_map ι, hmap, hsmall]

end

end Erdos85
