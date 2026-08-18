import Proofs.Erdos85OrderSixtyFourSixteenPairInjection

/-! # Selected pairs are the defect-complement edges on H16 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- On the distinguished order-sixteen defect component, a pair of
distinct vertices is selected as the two H16-neighbors of an ambient
vertex exactly when it is a nonedge of the defect graph. -/
theorem orderSixtyFour_seven_defect_components_pair_iff_not_defectAdj
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
      ∀ u v : c.supp, u ≠ v →
        ((∃ x : Fin 64,
          componentNeighborFinset G (secondOrderDefectGraph G) c x =
            {u.1, v.1}) ↔
          ¬ (secondOrderDefectGraph G).Adj u.1 v.1) := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, htwo, _hsmall⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro u v huv
  have huvval : u.1 ≠ v.1 := fun h ↦ huv (Subtype.ext h)
  constructor
  · rintro ⟨x, hx⟩ hDuv
    have hxu : G.Adj x u.1 := by
      have hu : u.1 ∈ componentNeighborFinset G D c x := by
        rw [hx]
        simp [huvval]
      exact (G.mem_neighborFinset x u.1).mp (Finset.mem_filter.mp hu).1
    have hxv : G.Adj x v.1 := by
      have hv : v.1 ∈ componentNeighborFinset G D c x := by
        rw [hx]
        simp
      exact (G.mem_neighborFinset x v.1).mp (Finset.mem_filter.mp hv).1
    have hxmem : x ∈ G.neighborFinset u.1 ∩ G.neighborFinset v.1 :=
      Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset u.1 x).mpr hxu.symm,
          (G.mem_neighborFinset v.1 x).mpr hxv.symm⟩
    have hcommon := card_common_eq_if_secondOrderDefect
      G hfree u.1 v.1 huvval
    have hmemD : v.1 ∈ D.neighborFinset u.1 :=
      (D.mem_neighborFinset u.1 v.1).mpr hDuv
    rw [if_pos hmemD] at hcommon
    have : 0 < (G.neighborFinset u.1 ∩ G.neighborFinset v.1).card :=
      Finset.card_pos.mpr ⟨x, hxmem⟩
    omega
  · intro hDuv
    have hcommon := card_common_eq_if_secondOrderDefect
      G hfree u.1 v.1 huvval
    have hnotmemD : v.1 ∉ D.neighborFinset u.1 := by
      intro hmem
      exact hDuv ((D.mem_neighborFinset u.1 v.1).mp hmem)
    rw [if_neg hnotmemD] at hcommon
    obtain ⟨x, hx⟩ :
        ∃ x, x ∈ G.neighborFinset u.1 ∩ G.neighborFinset v.1 := by
      exact Finset.card_pos.mp (by omega)
    refine ⟨x, ?_⟩
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      rcases hy with rfl | rfl
      · apply Finset.mem_filter.mpr
        refine ⟨(G.mem_neighborFinset x u.1).mpr
          ((G.mem_neighborFinset u.1 x).mp (Finset.mem_inter.mp hx).1).symm, ?_⟩
        exact (ConnectedComponent.mem_supp_iff c u.1).mp u.2
      · apply Finset.mem_filter.mpr
        refine ⟨(G.mem_neighborFinset x v.1).mpr
          ((G.mem_neighborFinset v.1 x).mp (Finset.mem_inter.mp hx).2).symm, ?_⟩
        exact (ConnectedComponent.mem_supp_iff c v.1).mp v.2
    · rw [htwo x]
      simp [huvval]

end

end Erdos85
