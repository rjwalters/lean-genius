import Proofs.Erdos85OrderSixtyFourPairQuotient
import Proofs.Erdos85OrderSixteenTwoFactorCensus
import Proofs.Erdos85FiniteSizeEnumeration

/-! # Four surviving H16 cycle partitions -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The corrected exterior-Gram quotient eliminates eight of the twelve
cycle partitions on the distinguished order-16 block. -/
theorem orderSixtyFour_seven_components_fourSurvivor_cyclePartition
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
      let H := G.induce c.supp
      ∃ rs : List ℕ,
        ((↑rs : Multiset ℕ) =
          (Finset.univ : Finset H.ConnectedComponent).val.map
            (fun a ↦ a.supp.ncard)) ∧
        (rs = [16] ∨ rs = [10, 6] ∨ rs = [8, 8] ∨
          rs = [5, 5, 3, 3]) := by
  classical
  obtain ⟨c, hc16, hledger⟩ :=
    orderSixtyFour_seven_components_pairQuotient_conditions
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  let H := G.induce c.supp
  let R := exteriorPairGraph G c.supp
  obtain ⟨instComp, hrow, hbal, hdiag, hbound⟩ := hledger
  letI : DecidableEq H.ConnectedComponent := instComp
  have hcardH : Fintype.card c.supp = 16 := by
    calc
      Fintype.card c.supp = c.supp.ncard := by
        simpa [Nat.card_eq_fintype_card] using
          (Nat.card_coe_set_eq c.supp)
      _ = 16 := hc16
  have htwo : ∀ x : c.supp, H.degree x = 2 := by
    intro x
    have hmul := orderSixtyFour_eight_mul_componentNeighborFinset_card
      G hfree hmin hcover c x.1
    rw [hc16] at hmul
    change 8 * ((G.neighborFinset x.1).filter fun y =>
      (secondOrderDefectGraph G).connectedComponentMk y = c).card = 16 at hmul
    have hfilter :
        ((G.neighborFinset x.1).filter fun y =>
          (secondOrderDefectGraph G).connectedComponentMk y = c).card = 2 := by
      omega
    have hmap := G.map_neighborFinset_induce x
    have hdegree : H.degree x =
        (G.neighborFinset x.1 ∩ c.supp.toFinset).card := by
      rw [← H.card_neighborFinset_eq_degree, ← hmap, Finset.card_map]
    have hinter : G.neighborFinset x.1 ∩ c.supp.toFinset =
        (G.neighborFinset x.1).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c) := by
      ext y
      simp [SimpleGraph.ConnectedComponent.mem_supp_iff]
    rw [hdegree, hinter, hfilter]
  have hHfree : ¬ containsC4 c.supp H := by
    intro hC4
    obtain ⟨f, hf, hadj⟩ := hC4
    apply hfree
    refine ⟨Subtype.val ∘ f, Subtype.val_injective.comp hf, ?_⟩
    intro i j hij
    exact hadj i j hij
  obtain ⟨rs, hrsClass, hrsizes⟩ :=
    exists_orderSixteenCyclePartition_of_twoRegular_of_not_containsC4
      H hcardH htwo hHfree
  have hfeas : ∃ q : Fin rs.length → Fin rs.length → ℕ,
      SixRegularPairQuotientFeasible (fun i ↦ rs.get i) q := by
    obtain ⟨e, he⟩ := exists_equiv_fin_of_multiset_eq_map
      (fun a : H.ConnectedComponent ↦ a.supp.ncard) rs hrsizes
    exact exists_sixRegularPairQuotientFeasible_of_equiv
      (fun a : H.ConnectedComponent ↦ a.supp.ncard)
      (componentQuotientMatrix R H) (fun i ↦ rs.get i) e he
      hrow hbal hdiag hbound
  refine ⟨rs, hrsizes, ?_⟩
  rcases hrsClass with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · obtain ⟨q, hq⟩ := hfeas
    have hq' : SixRegularPairQuotientFeasible ![13, 3] q := by
      simpa [SixRegularPairQuotientFeasible] using hq
    exact (not_pairQuotientFeasible_thirteen_three q hq').elim
  · obtain ⟨q, hq⟩ := hfeas
    have hq' : SixRegularPairQuotientFeasible ![11, 5] q := by
      simpa [SixRegularPairQuotientFeasible] using hq
    exact (not_pairQuotientFeasible_eleven_five q hq').elim
  · exact Or.inr (Or.inl rfl)
  · obtain ⟨q, hq⟩ := hfeas
    have hs : (fun i : Fin 3 ↦ [10, 3, 3].get i) = ![10, 3, 3] := by
      funext i; fin_cases i <;> rfl
    have hq' : SixRegularPairQuotientFeasible ![10, 3, 3] q := by
      exact hs ▸ hq
    exact (not_pairQuotientFeasible_ten_three_three q hq').elim
  · obtain ⟨q, hq⟩ := hfeas
    have hq' : SixRegularPairQuotientFeasible ![9, 7] q := by
      simpa [SixRegularPairQuotientFeasible] using hq
    exact (not_pairQuotientFeasible_nine_seven q hq').elim
  · exact Or.inr (Or.inr (Or.inl rfl))
  · obtain ⟨q, hq⟩ := hfeas
    have hs : (fun i : Fin 3 ↦ [8, 5, 3].get i) = ![8, 5, 3] := by
      funext i; fin_cases i <;> rfl
    have hq' : SixRegularPairQuotientFeasible ![8, 5, 3] q := by
      exact hs ▸ hq
    exact (not_pairQuotientFeasible_eight_five_three q hq').elim
  · obtain ⟨q, hq⟩ := hfeas
    have hs : (fun i : Fin 3 ↦ [7, 6, 3].get i) = ![7, 6, 3] := by
      funext i; fin_cases i <;> rfl
    have hq' : SixRegularPairQuotientFeasible ![7, 6, 3] q := by
      exact hs ▸ hq
    exact (not_pairQuotientFeasible_seven_six_three q hq').elim
  · obtain ⟨q, hq⟩ := hfeas
    have hs : (fun i : Fin 4 ↦ [7, 3, 3, 3].get i) = ![7, 3, 3, 3] := by
      funext i; fin_cases i <;> rfl
    have hq' : SixRegularPairQuotientFeasible ![7, 3, 3, 3] q := by
      exact hs ▸ hq
    exact (not_pairQuotientFeasible_seven_three_three_three q hq').elim
  · obtain ⟨q, hq⟩ := hfeas
    have hs : (fun i : Fin 3 ↦ [6, 5, 5].get i) = ![6, 5, 5] := by
      funext i; fin_cases i <;> rfl
    have hq' : SixRegularPairQuotientFeasible ![6, 5, 5] q := by
      exact hs ▸ hq
    exact (not_pairQuotientFeasible_six_five_five q hq').elim
  · exact Or.inr (Or.inr (Or.inr rfl))

end

end Erdos85
