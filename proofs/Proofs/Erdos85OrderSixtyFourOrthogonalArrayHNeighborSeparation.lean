import Proofs.Erdos85OrderSixtyFourOrthogonalArrayHRestriction
import Proofs.Erdos85OrderSixtyFourSixteenBlockCycles

/-! # OA labels separate the two neighbors of every H16 vertex -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In every small-block label column, the two neighbors of a vertex in
the H16 two-factor have different labels.  Otherwise that H16 vertex and
the common small-block label would witness a four-cycle. -/
theorem orderSixtyFour_seven_defect_components_orthogonalArray_H_neighbor_separation
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
          (∀ i (x : (κ i).1.supp),
            ((Finset.univ : Finset c.supp).filter
              (fun u => ℓ i u.1 = x)).card = 2) ∧
          (∀ y : c.supp, (G.induce c.supp).degree y = 2) ∧
          ∀ i (y u v : c.supp),
            (G.induce c.supp).Adj y u →
            (G.induce c.supp).Adj y v →
            u ≠ v → ℓ i u.1 ≠ ℓ i v.1 := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, κ, ℓ, hpair, hiff, hbalance⟩ :=
    orderSixtyFour_seven_defect_components_orthogonalArray_H_restriction
      G hfree hmin hcover hcount
  obtain ⟨c', hc'16, hdeg'⟩ :=
    orderSixtyFour_seven_defect_components_sixteenBlock_twoRegular
      G hfree hmin hcover hcount
  obtain ⟨d, hd16, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_partition
      G hfree hmin hcover hcount
  have hcd : c = d := by
    by_contra hne
    have hc8 := hsmall c hne
    omega
  subst d
  have hc' : c' = c := by
    by_contra hne
    have hc'8 := hsmall c' hne
    omega
  subst c'
  refine ⟨c, hc16, κ, ℓ, hpair, hbalance, hdeg', ?_⟩
  intro i y u v hyu hyv huv hlabel
  have huvVal : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
  let x : (κ i).1.supp := ℓ i u.1
  have hxy : y.1 ≠ x.1 := by
    intro h
    have hxcomp : D.connectedComponentMk x.1 = (κ i).1 :=
      (ConnectedComponent.mem_supp_iff (κ i).1 x.1).mp x.2
    have hycomp : D.connectedComponentMk y.1 = c :=
      (ConnectedComponent.mem_supp_iff c y.1).mp y.2
    exact (κ i).2 (by rw [← hxcomp, ← h, hycomp])
  have hxu : G.Adj x.1 u.1 := (hiff i x u.1).mpr rfl
  have hxv : G.Adj x.1 v.1 := by
    apply (hiff i x v.1).mpr
    exact hlabel.symm
  exact hfree (containsC4_of_two_common huvVal hxy hyu hyv hxu hxv)

end

end Erdos85
