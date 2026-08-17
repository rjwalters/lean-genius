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
          (∀ (y u : c.supp), (G.induce c.supp).Adj y u →
            ∀ i j, ℓ i (ℓ j u.1).1 ≠ ℓ i y.1) ∧
          ∀ i j (x : (κ i).1.supp),
            ((Finset.univ : Finset c.supp).filter
              (fun u ↦ ℓ i (ℓ j u.1).1 = x)).card = 2 := by
  classical
  obtain ⟨c, hc16, κ, ℓ, _hpair, hiff, hbalance⟩ :=
    orderSixtyFour_seven_defect_components_orthogonalArray_H_restriction
      G hfree hmin hcover hcount
  let D := secondOrderDefectGraph G
  have hH_K (i : Fin 6) (y : c.supp) (x : (κ i).1.supp) :
      y.1 ≠ x.1 := by
    intro h
    have hycomp : D.connectedComponentMk y.1 = c :=
      (ConnectedComponent.mem_supp_iff c y.1).mp y.2
    have hxcomp : D.connectedComponentMk x.1 = (κ i).1 :=
      (ConnectedComponent.mem_supp_iff (κ i).1 x.1).mp x.2
    have hcEq : c = (κ i).1 :=
      hycomp.symm.trans ((congrArg D.connectedComponentMk h).trans hxcomp)
    exact (κ i).2 hcEq.symm
  have hedge : ∀ (y u : c.supp), (G.induce c.supp).Adj y u →
      ∀ i j, ℓ i (ℓ j u.1).1 ≠ ℓ i y.1 := by
    intro y u hyu i j heq
    let x : (κ i).1.supp := ℓ i y.1
    let x' : (κ j).1.supp := ℓ j u.1
    have hyx : G.Adj y.1 x.1 := ((hiff i x y.1).mpr rfl).symm
    have hx'u : G.Adj x'.1 u.1 := (hiff j x' u.1).mpr rfl
    have hcross : G.Adj x.1 x'.1 := (hiff i x x'.1).mpr heq
    have huy : u.1 ≠ y.1 := by
      intro h
      exact (G.induce c.supp).ne_of_adj hyu (Subtype.ext h.symm)
    have hxx' : x.1 ≠ x'.1 := G.ne_of_adj hcross
    exact hfree (containsC4_of_rim hyx hcross hx'u hyu.symm
      (hH_K j y x') ((hH_K i u x).symm) ((hH_K i y x).symm)
      hxx' huy (hH_K j u x'))
  refine ⟨c, hc16, κ, ℓ, hiff, hbalance, hedge, ?_⟩
  intro i j x
  exact oa_compositeLabel_fiber_card_eq G
    (fun k : Fin 6 ↦ (κ k).1.supp) c.supp ℓ hiff hbalance i j x

end

end Erdos85
