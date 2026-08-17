import Proofs.Erdos85OrderSixtyFourHMatchingFamily

/-! # Exact selected-pair identities for the six H16 matchings -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every edge of each small-block matching is exactly the two-element
H16 neighbor set selected by a vertex of that small block. -/
theorem orderSixtyFour_seven_defect_components_H_matchingPairFamily
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
        ∃ μ : Fin 6 → Equiv.Perm c.supp,
          (∀ i, Function.Involutive (μ i)) ∧
          (∀ i u, μ i u ≠ u) ∧
          (∀ i j, i ≠ j → ∀ u, μ i u ≠ μ j u) ∧
          ∀ i u, ∃ x : (κ i).1.supp,
            componentNeighborFinset G (secondOrderDefectGraph G) c x.1 =
              {u.1, (μ i u).1} := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, κ, μ, hinvol, hfreePoint, hdisj, hadj⟩ :=
    orderSixtyFour_seven_defect_components_H_matchingFamily
      G hfree hmin hcover hcount
  obtain ⟨c', hc'16, htwo', hsmall'⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  have hcc' : c = c' := by
    by_contra hne
    have hc8 := (hsmall' c hne).1
    omega
  have htwo (x : Fin 64) :
      (componentNeighborFinset G D c x).card = 2 := by
    rw [hcc']
    exact htwo' x
  refine ⟨c, hc16, κ, μ, hinvol, hfreePoint, hdisj, ?_⟩
  intro i u
  obtain ⟨x, hxu, hxmu⟩ := hadj i u
  refine ⟨x, ?_⟩
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · apply Finset.mem_filter.mpr
      refine ⟨(G.mem_neighborFinset x.1 u.1).mpr hxu, ?_⟩
      exact (ConnectedComponent.mem_supp_iff c u.1).mp u.2
    · apply Finset.mem_filter.mpr
      refine ⟨(G.mem_neighborFinset x.1 (μ i u).1).mpr hxmu, ?_⟩
      exact (ConnectedComponent.mem_supp_iff c (μ i u).1).mp (μ i u).2
  · rw [htwo]
    have hne : u.1 ≠ (μ i u).1 := by
      intro h
      exact hfreePoint i u (Subtype.ext h.symm)
    simp [hne]

end

end Erdos85
