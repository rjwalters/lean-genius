import Proofs.Erdos85OrderSixtyFourColoredSupport

/-! # The internal two-factor on the order-16 defect block -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the seven-component branch, the ambient graph induced on the unique
order-16 defect component is 2-regular.  This is the structural route from
the nonlinear defect-primary problem to cycle spectra. -/
theorem orderSixtyFour_seven_defect_components_sixteenBlock_twoRegular
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
      ∀ x : c.supp, (G.induce c.supp).degree x = 2 := by
  let instG := ‹DecidableRel G.Adj›
  let instAnti := ‹DecidableRel (antipodalGraph G).Adj›
  let instT := ‹DecidableRel (triangleFreeEdgeGraph G).Adj›
  let instComp := ‹DecidableEq (secondOrderDefectGraph G).ConnectedComponent›
  classical
  letI := instG
  letI := instAnti
  letI := instT
  letI := instComp
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, hcLocal, _hsmall⟩ :=
    orderSixtyFour_seven_defect_components_local_degrees
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro x
  have hmap := G.map_neighborFinset_induce x
  have hdegree : (G.induce c.supp).degree x =
      (G.neighborFinset x.1 ∩ c.supp.toFinset).card := by
    rw [← (G.induce c.supp).card_neighborFinset_eq_degree,
      ← hmap, Finset.card_map]
  have hinter : G.neighborFinset x.1 ∩ c.supp.toFinset =
      (G.neighborFinset x.1).filter
        (fun y => D.connectedComponentMk y = c) := by
    ext y
    simp [D, ConnectedComponent.mem_supp_iff]
  rw [hdegree, hinter]
  simpa [D] using hcLocal x.1 x.2

/-- Equivalently, the internal order-16 ambient graph is a graph of cycles
in Mathlib's `IsCycles` sense. -/
theorem orderSixtyFour_seven_defect_components_sixteenBlock_isCycles
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
      c.supp.ncard = 16 ∧ (G.induce c.supp).IsCycles := by
  classical
  obtain ⟨c, hc16, hreg⟩ :=
    orderSixtyFour_seven_defect_components_sixteenBlock_twoRegular
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro x _hx
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card,
    (G.induce c.supp).card_neighborSet_eq_degree, hreg x]

end

end Erdos85
