import Proofs.Erdos85OrderSixtyFourTenSixComponentLabeling
import Proofs.Erdos85OrderSixtyFourSixteenBlockCycles

/-! # Graph-facing labeling of the order-64 `[10,6]` branch -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Once the distinguished order-16 block has component-size multiset
`[10,6]`, the ambient order-64 hypotheses provide the exact certificate
labeling of its induced graph. -/
theorem orderSixtyFour_seven_components_tenSixComponentLabeling
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hmin : ∀ x : Fin 64, 8 ≤ G.degree x)
    (hcover : ∀ {u v}, G.Adj u v →
      G.degree u = 8 ∨ G.degree v = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 7)
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    (hc16 : c.supp.ncard = 16)
    (hsizes : (↑[10, 6] : Multiset ℕ) =
      (Finset.univ : Finset (G.induce c.supp).ConnectedComponent).val.map
        (fun a ↦ a.supp.ncard)) :
    Nonempty (TenSixComponentLabeling (G.induce c.supp)) := by
  classical
  obtain ⟨c', hc'16, htwo⟩ :=
    orderSixtyFour_seven_defect_components_sixteenBlock_twoRegular
      G hfree hmin hcover hcount
  obtain ⟨d, _hd16, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  have heq_of_16 : ∀ {a : (secondOrderDefectGraph G).ConnectedComponent},
      a.supp.ncard = 16 → a = d := by
    intro a ha
    by_contra had
    have := hsmall a had
    omega
  have hcc' : c = c' :=
    (heq_of_16 hc16).trans (heq_of_16 hc'16).symm
  subst c'
  exact exists_tenSixComponentLabeling_of_componentSizes
    (G.induce c.supp) htwo hsizes

end

end Erdos85
