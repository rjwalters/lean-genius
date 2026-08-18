import Proofs.Erdos85OrderSixtyFourSmallBlockCoordinateCharacterization

/-! # Coordinate involutions on the two distinguished small blocks -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Under the `8 × 8` coordinatization, restricting the first coordinate to
the first small block and the second coordinate to the second small block
gives fixed-point-free involutions.  They are precisely the blocks' internal
perfect matchings. -/
theorem orderSixtyFour_seven_defect_components_coordinate_involutions
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
      ∀ e, e ≠ c → e.supp.ncard = 8 ∧
        ∀ f, f ≠ c → f.supp.ncard = 8 ∧
          ∀ (_hef : e ≠ f), ∃ φ : Fin 64 ≃ e.supp × f.supp,
            Function.Involutive (fun x : e.supp => (φ x.1).1) ∧
            (∀ x : e.supp, (φ x.1).1 ≠ x) ∧
            Function.Involutive (fun y : f.supp => (φ y.1).2) ∧
            ∀ y : f.supp, (φ y.1).2 ≠ y := by
  classical
  obtain ⟨c, hc16, hsmall⟩ :=
    orderSixtyFour_seven_defect_components_smallBlock_coordinate_iff
      G hfree hmin hcover hcount
  refine ⟨c, hc16, ?_⟩
  intro e hec
  obtain ⟨he8, hecoords⟩ := hsmall e hec
  refine ⟨he8, ?_⟩
  intro f hfc
  obtain ⟨hf8, hfcoords⟩ := hecoords f hfc
  refine ⟨hf8, ?_⟩
  intro hef
  obtain ⟨φ, hE, hF⟩ := hfcoords hef
  let mE : e.supp → e.supp := fun x => (φ x.1).1
  let mF : f.supp → f.supp := fun y => (φ y.1).2
  have hEinvol : Function.Involutive mE := by
    intro x
    have hmx : G.Adj (mE x).1 x.1 :=
      (hE x.1 (mE x)).mpr rfl
    exact ((hE (mE x).1 x).mp hmx.symm).symm
  have hEfree : ∀ x : e.supp, mE x ≠ x := by
    intro x hfix
    have hloop : G.Adj x.1 x.1 :=
      (hE x.1 x).mpr hfix.symm
    exact G.loopless.irrefl x.1 hloop
  have hFinvol : Function.Involutive mF := by
    intro y
    have hmy : G.Adj (mF y).1 y.1 :=
      (hF y.1 (mF y)).mpr rfl
    exact ((hF (mF y).1 y).mp hmy.symm).symm
  have hFfree : ∀ y : f.supp, mF y ≠ y := by
    intro y hfix
    have hloop : G.Adj y.1 y.1 :=
      (hF y.1 y).mpr hfix.symm
    exact G.loopless.irrefl y.1 hloop
  exact ⟨φ, hEinvol, hEfree, hFinvol, hFfree⟩

end

end Erdos85
