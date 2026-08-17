import Proofs.Erdos85OutsideReturnGramIdentity

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
      let B := (G.adjMatrix ℂ).toBlock p (fun x ↦ x ∈ q)
      let Cg := G.induce q
      let C := Cg.adjMatrix ℂ
      (∀ x : Fin 64,
        (componentNeighborFinset G (secondOrderDefectGraph G) c x).card = 2) ∧
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
  subst c'
  subst c''
  refine ⟨c, hc16, hinc, hout, ?_, hcross⟩
  intro hC4
  obtain ⟨f, hf, hadj⟩ := hC4
  apply hfree
  refine ⟨Subtype.val ∘ f, Subtype.val_injective.comp hf, ?_⟩
  intro i j hij
  exact hadj i j hij

end

end Erdos85
