import Proofs.Erdos85OrderSixtyFourOrthogonalArrayHRestriction

/-! # Balanced composite label fibers on H16 -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In an OA labeling, composing the label into block `j` with the label
back into block `i` does not change the H16 fiber size.  Symmetry of ambient
adjacency turns the composite equation into an ordinary `j`-label equation. -/
theorem oa_compositeLabel_fiber_card_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {I : Type*} [Fintype I]
    (K : I → Set V) [∀ i, Fintype (K i)]
    (H : Set V) [Fintype H]
    (label : ∀ i, V → K i)
    (hadj : ∀ i (x : K i) z, G.Adj x.1 z ↔ label i z = x)
    (hbalanced : ∀ i (x : K i),
      ((Finset.univ : Finset H).filter
        (fun u ↦ label i u.1 = x)).card = 2)
    (i j : I) (x : K i) :
    ((Finset.univ : Finset H).filter
      (fun u ↦ label i (label j u.1).1 = x)).card = 2 := by
  classical
  have heq :
      ((Finset.univ : Finset H).filter
        (fun u ↦ label i (label j u.1).1 = x)) =
      (Finset.univ.filter
        (fun u : H ↦ label j u.1 = label j x.1)) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hcomp
      have hxadj : G.Adj x.1 (label j u.1).1 :=
        (hadj i x (label j u.1).1).mpr hcomp
      exact ((hadj j (label j u.1) x.1).mp hxadj.symm).symm
    · intro hj
      have hadj' : G.Adj (label j u.1).1 x.1 :=
        (hadj j (label j u.1) x.1).mpr hj.symm
      exact (hadj i x (label j u.1).1).mp hadj'.symm
  rw [heq]
  exact hbalanced j (label j x.1)

/-- The order-64 seven-component branch therefore carries 36 families of
balanced two-element composite fibers on H16, one for every ordered pair of
small defect blocks. -/
theorem orderSixtyFour_seven_components_OA_composite_fibers
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
          (∀ i (x : (κ i).1.supp) z, G.Adj x.1 z ↔ ℓ i z = x) ∧
          (∀ i (x : (κ i).1.supp),
            ((Finset.univ : Finset c.supp).filter
              (fun u ↦ ℓ i u.1 = x)).card = 2) ∧
          ∀ i j (x : (κ i).1.supp),
            ((Finset.univ : Finset c.supp).filter
              (fun u ↦ ℓ i (ℓ j u.1).1 = x)).card = 2 := by
  classical
  obtain ⟨c, hc16, κ, ℓ, _hpair, hiff, hbalance⟩ :=
    orderSixtyFour_seven_defect_components_orthogonalArray_H_restriction
      G hfree hmin hcover hcount
  refine ⟨c, hc16, κ, ℓ, hiff, hbalance, ?_⟩
  intro i j x
  exact oa_compositeLabel_fiber_card_eq G
    (fun k : Fin 6 ↦ (κ k).1.supp) c.supp ℓ hiff hbalance i j x

end

end Erdos85
