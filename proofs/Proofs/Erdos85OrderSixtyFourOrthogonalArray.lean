import Proofs.Erdos85OrderSixtyFourSmallBlockTripleIncidence

/-! # The coherent six-column orthogonal array at order 64 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The six order-eight defect components form a coherent strength-two
orthogonal array: every ambient vertex has one neighbor-label in each block,
and any two distinct label columns coordinatize all 64 vertices bijectively. -/
theorem orderSixtyFour_seven_defect_components_orthogonalArray
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
          (∀ i z, G.Adj (ℓ i z).1 z) ∧
          ∀ i j, i ≠ j →
            Function.Bijective (fun z : Fin 64 => (ℓ i z, ℓ j z)) := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, _hH, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  let K := {k : D.ConnectedComponent // k ≠ c}
  have hKcard : Fintype.card K = 6 := by
    rw [Fintype.card_subtype_compl (fun k : D.ConnectedComponent => k = c), hcount]
    simp
  let κ : Fin 6 ≃ K :=
    (finCongr hKcard.symm).trans (Fintype.equivFin K).symm
  let S (i : Fin 6) (z : Fin 64) : Finset (Fin 64) :=
    componentNeighborFinset G D (κ i).1 z
  have hScard (i : Fin 6) (z : Fin 64) : (S i z).card = 1 :=
    (hsmall (κ i).1 (κ i).2).2 z
  let v (i : Fin 6) (z : Fin 64) : Fin 64 :=
    Classical.choose (Finset.card_eq_one.mp (hScard i z))
  have hv_mem (i : Fin 6) (z : Fin 64) : v i z ∈ S i z := by
    have hs := Classical.choose_spec (Finset.card_eq_one.mp (hScard i z))
    rw [hs]
    simp [v]
  have hv_supp (i : Fin 6) (z : Fin 64) : v i z ∈ (κ i).1.supp := by
    rw [ConnectedComponent.mem_supp_iff]
    exact (Finset.mem_filter.mp (hv_mem i z)).2
  let ℓ : ∀ i : Fin 6, Fin 64 → (κ i).1.supp :=
    fun i z => ⟨v i z, hv_supp i z⟩
  have hℓadj (i : Fin 6) (z : Fin 64) : G.Adj (ℓ i z).1 z := by
    exact ((G.mem_neighborFinset z (v i z)).mp
      (Finset.mem_filter.mp (hv_mem i z)).1).symm
  refine ⟨c, hc16, κ, ℓ, hℓadj, ?_⟩
  intro i j hij
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · intro z w hzw
    have hk : (κ i).1 ≠ (κ j).1 := by
      intro h
      exact hij (κ.injective (Subtype.ext h))
    apply crossDefectComponent_common_completion_injective
      G hfree hk (ℓ i z) (ℓ j z)
    · exact ⟨hℓadj i z, hℓadj j z⟩
    · have hi : ℓ i z = ℓ i w := congrArg Prod.fst hzw
      have hj : ℓ j z = ℓ j w := congrArg Prod.snd hzw
      exact ⟨hi ▸ hℓadj i w, hj ▸ hℓadj j w⟩
  · have hi8 : Fintype.card (κ i).1.supp = 8 := by
      have hisize := (hsmall (κ i).1 (κ i).2).1
      have hicard : Fintype.card (κ i).1.supp = (κ i).1.supp.ncard := by
        simpa [Nat.card_eq_fintype_card] using
          Nat.card_coe_set_eq (κ i).1.supp
      omega
    have hj8 : Fintype.card (κ j).1.supp = 8 := by
      have hjsize := (hsmall (κ j).1 (κ j).2).1
      have hjcard : Fintype.card (κ j).1.supp = (κ j).1.supp.ncard := by
        simpa [Nat.card_eq_fintype_card] using
          Nat.card_coe_set_eq (κ j).1.supp
      omega
    simp [hi8, hj8]

end

end Erdos85
