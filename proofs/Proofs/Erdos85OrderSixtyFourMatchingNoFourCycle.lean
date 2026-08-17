import Proofs.Erdos85OrderSixtyFourOrthogonalArrayReciprocity

/-! # Four-cycle exclusion in the order-64 matching network -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The coherent block matchings cannot close a nondegenerate four-step
chain: such a closure would give two distinct common neighbors to the two
opposite vertices and hence a forbidden four-cycle. -/
theorem orderSixtyFour_seven_defect_components_matching_noFourCycle
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
        ∃ m : ∀ i j : Fin 6, (κ i).1.supp ≃ (κ j).1.supp,
          (∀ i j x, G.Adj x.1 (m i j x).1) ∧
          (∀ i j x, m j i (m i j x) = x) ∧
          (∀ i x, m i i x ≠ x) ∧
          ∀ i j k l (x : (κ i).1.supp),
            let y := m i j x
            let z := m j k y
            let w := m k l z
            x.1 ≠ z.1 → y.1 ≠ w.1 → m l i w ≠ x := by
  classical
  obtain ⟨c, hc16, κ, ℓ, m, _hpair, hiff, hmLabel, hrecip, hdiag⟩ :=
    orderSixtyFour_seven_defect_components_orthogonalArray_reciprocity
      G hfree hmin hcover hcount
  have hmadj (i j : Fin 6) (x : (κ i).1.supp) :
      G.Adj x.1 (m i j x).1 := by
    have h : G.Adj (m i j x).1 x.1 :=
      (hiff j (m i j x) x.1).mpr (hmLabel i j x).symm
    exact h.symm
  refine ⟨c, hc16, κ, m, hmadj, hrecip, hdiag, ?_⟩
  intro i j k l x
  dsimp only
  intro hxz hyw hclose
  let y := m i j x
  let z := m j k y
  let w := m k l z
  have hxy : G.Adj x.1 y.1 := hmadj i j x
  have hyz : G.Adj y.1 z.1 := hmadj j k y
  have hzw : G.Adj z.1 w.1 := hmadj k l z
  have hwx : G.Adj w.1 x.1 := by
    have h := hmadj l i w
    rw [hclose] at h
    exact h
  exact hfree (containsC4_of_two_common hxz hyw
    hxy.symm hyz hwx hzw.symm)

end

end Erdos85
