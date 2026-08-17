import Proofs.Erdos85OutsideReturnGramIdentity
import Proofs.Erdos85OrderSixtyFourExteriorPairGraph

/-! # A single graph-facing package for the order-64 outside block -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The unique H16 component comes with exactly the finite outside data used
by the `[10,6]` certificate encoding: two incidences per outside vertex, a
six-regular C4-free outside graph, and the exact cross-block equation. -/
theorem orderSixtyFour_seven_components_outside_feasibility
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
      let p : Fin 64 → Prop := fun x ↦ x ∈ c.supp
      let q : Set (Fin 64) := {x | ¬p x}
      let H := (G.induce c.supp).adjMatrix ℂ
      let R := exteriorPairGraph G c.supp
      let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
      let Cg := G.induce q
      let C := Cg.adjMatrix ℂ
      ∃ _outsideLabel : q ≃ Fin 48,
      Fintype.card q = 48 ∧
      (∀ x : Fin 64,
        (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2) ∧
      Function.Injective
        (componentNeighborFinset G (secondOrderDefectGraph G) c) ∧
      (∀ u : c.supp, R.degree u = 6) ∧
      (∀ z : q, Cg.degree z = 6) ∧
      (¬containsC4 q Cg) ∧
      H * B + B * C = (fun _ _ ↦ (1 : ℂ)) := by
  classical
  obtain ⟨c, hc16, hcross, _hreturn⟩ :=
    orderSixtyFour_seven_components_outsideReturn_eq_sixJ_sub_HQ
      G hfree hmin hcover hcount
  obtain ⟨c', hc'16, hout⟩ :=
    orderSixtyFour_seven_components_outside_induce_sixRegular
      G hfree hmin hcover hcount
  obtain ⟨c'', hc''16, hinc, _hsmall⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  obtain ⟨cR, hcR16, _hQ, hRreg⟩ :=
    orderSixtyFour_seven_components_exteriorGram_eq_six_add_sixRegular
      G hfree hmin hcover hcount
  obtain ⟨d, _hd16, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  have heq_of_16 : ∀ {a}, a.supp.ncard = 16 → a = d := by
    intro a ha
    by_contra hne
    have := hsmall a hne
    omega
  have hcc' : c = c' :=
    (heq_of_16 hc16).trans (heq_of_16 hc'16).symm
  have hcc'' : c = c'' :=
    (heq_of_16 hc16).trans (heq_of_16 hc''16).symm
  have hccR : c = cR :=
    (heq_of_16 hc16).trans (heq_of_16 hcR16).symm
  subst c'
  subst c''
  subst cR
  have hqcard : Fintype.card {x : Fin 64 // x ∉ c.supp} = 48 := by
    calc
      Fintype.card {x : Fin 64 // x ∉ c.supp} = c.suppᶜ.ncard := by
        rw [← Nat.card_eq_fintype_card]
        exact Nat.card_coe_set_eq c.suppᶜ
      _ = Nat.card (Fin 64) - c.supp.ncard := Set.ncard_compl c.supp
      _ = 48 := by simp [hc16]
  have houtsideLabel : {x : Fin 64 // x ∉ c.supp} ≃ Fin 48 :=
    Fintype.equivOfCardEq (by simpa using hqcard)
  have hinj : Function.Injective
      (componentNeighborFinset G (secondOrderDefectGraph G) c) := by
    intro y z heq
    by_contra hyz
    let Sy := componentNeighborFinset G (secondOrderDefectGraph G) c y
    have hSycard : Sy.card = 2 := hinc y
    have hsub : Sy ⊆ G.neighborFinset y ∩ G.neighborFinset z := by
      intro w hw
      have hwy : G.Adj y w :=
        (G.mem_neighborFinset y w).mp ((Finset.mem_filter.mp hw).1)
      have hwzS : w ∈
          componentNeighborFinset G (secondOrderDefectGraph G) c z := by
        rw [← heq]
        exact hw
      have hwz : G.Adj z w :=
        (G.mem_neighborFinset z w).mp ((Finset.mem_filter.mp hwzS).1)
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset y w).mpr hwy,
          (G.mem_neighborFinset z w).mpr hwz⟩
    have hle := Finset.card_le_card hsub
    have hone := common_le_one_of_not_containsC4 hfree y z hyz
    omega
  refine ⟨c, hc16, houtsideLabel, hqcard, hinc, hinj, hRreg, hout, ?_, hcross⟩
  intro hC4
  obtain ⟨f, hf, hadj⟩ := hC4
  apply hfree
  refine ⟨Subtype.val ∘ f, Subtype.val_injective.comp hf, ?_⟩
  intro i j hij
  exact hadj i j hij

end

end Erdos85
