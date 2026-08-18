import Proofs.Erdos85OrderSixtyFourPairPartition
import Proofs.Erdos85ComponentGramCommutation
import Proofs.Erdos85PairQuotientBridge

/-! # The actual H16 exterior-pair quotient -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the seven-defect-component branch, the distinguished H16 internal
two-factor and its exterior-pair graph satisfy the full quotient ledger used
by the finite partition terminals. -/
theorem orderSixtyFour_seven_components_pairQuotient_conditions
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
      let R := exteriorPairGraph G c.supp
      ∃ _ : DecidableEq H.ConnectedComponent,
      (∀ a : H.ConnectedComponent,
        ∑ b, componentQuotientMatrix R H a b = 6) ∧
      (∀ a b : H.ConnectedComponent,
        a.supp.ncard * componentQuotientMatrix R H a b =
          b.supp.ncard * componentQuotientMatrix R H b a) ∧
      (∀ a : H.ConnectedComponent,
        componentQuotientMatrix R H a a + 3 ≤ a.supp.ncard) ∧
      (∀ a b : H.ConnectedComponent,
        componentQuotientMatrix R H a b ≤ b.supp.ncard) := by
  classical
  obtain ⟨c, hc16, hQ, hRreg⟩ :=
    orderSixtyFour_seven_components_exteriorGram_eq_six_add_sixRegular
      G hfree hmin hcover hcount
  have htwo : ∀ x : c.supp, (G.induce c.supp).degree x = 2 := by
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
    have hdegree : (G.induce c.supp).degree x =
        (G.neighborFinset x.1 ∩ c.supp.toFinset).card := by
      rw [← (G.induce c.supp).card_neighborFinset_eq_degree,
        ← hmap, Finset.card_map]
    have hinter : G.neighborFinset x.1 ∩ c.supp.toFinset =
        (G.neighborFinset x.1).filter
          (fun y => (secondOrderDefectGraph G).connectedComponentMk y = c) := by
      ext y
      simp [SimpleGraph.ConnectedComponent.mem_supp_iff]
    rw [hdegree, hinter, hfilter]
  refine ⟨c, hc16, ?_⟩
  let H := G.induce c.supp
  let R := exteriorPairGraph G c.supp
  let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
  let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ ¬p x)
  let Q := B * Matrix.conjTranspose B
  have hHfree : ¬ containsC4 c.supp H := by
    intro hC4
    obtain ⟨f, hf, hadj⟩ := hC4
    apply hfree
    refine ⟨Subtype.val ∘ f, Subtype.val_injective.comp hf, ?_⟩
    intro i j hij
    exact hadj i j hij
  have hcommQ := orderSixtyFour_defectComponent_exteriorGram_comm
    G hfree hmin hcover c htwo |>.1
  change H.adjMatrix ℂ * Q = Q * H.adjMatrix ℂ at hcommQ
  change Q = (6 : ℂ) • (1 : Matrix c.supp c.supp ℂ) +
    R.adjMatrix ℂ at hQ
  have hcommC : R.adjMatrix ℂ * H.adjMatrix ℂ =
      H.adjMatrix ℂ * R.adjMatrix ℂ := by
    rw [hQ] at hcommQ
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul] at hcommQ
    exact (add_left_cancel hcommQ).symm
  have hcommR := adjMatrix_comm_real_of_complex R H hcommC
  have hsep : ∀ {x y : c.supp}, R.Adj x y →
      (H.neighborFinset x ∩ H.neighborFinset y).card = 0 := by
    intro x y hRxy
    apply Nat.eq_zero_of_not_pos
    intro hpos
    obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
    have hz' := Finset.mem_inter.mp hz
    have hinternal : ∃ z : c.supp, H.Adj x z ∧ H.Adj y z :=
      ⟨z, (H.mem_neighborFinset x z).mp hz'.1,
        (H.mem_neighborFinset y z).mp hz'.2⟩
    exact not_internalCommon_and_exteriorPair
      G hfree c.supp x y hRxy.1 ⟨hinternal, hRxy⟩
  letI : DecidableEq H.ConnectedComponent := Classical.decEq _
  exact ⟨inferInstance,
    componentQuotientMatrix_sixRegular_pair_conditions
      R H hHfree htwo hRreg hcommR hsep⟩

end

end Erdos85
