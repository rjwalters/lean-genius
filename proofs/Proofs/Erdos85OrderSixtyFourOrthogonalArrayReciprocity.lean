import Proofs.Erdos85OrderSixtyFourOrthogonalArrayMatching

/-! # Reciprocity of the order-64 orthogonal-array matchings -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Restricting one OA label column to another small block gives an
equivalence.  Graph symmetry makes the two directed restrictions mutual
inverses, including the fixed-point-free involution on a diagonal block. -/
theorem orderSixtyFour_seven_defect_components_orthogonalArray_reciprocity
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
          ∃ m : ∀ i j : Fin 6, (κ i).1.supp ≃ (κ j).1.supp,
            (∀ i j, i ≠ j →
              Function.Bijective (fun z : Fin 64 => (ℓ i z, ℓ j z))) ∧
            (∀ i (x : (κ i).1.supp) z, G.Adj x.1 z ↔ ℓ i z = x) ∧
            (∀ i j x, m i j x = ℓ j x.1) ∧
            (∀ i j x, m j i (m i j x) = x) ∧
            ∀ i x, m i i x ≠ x := by
  classical
  obtain ⟨c, hc16, κ, ℓ, hpair, hiff, hdiag⟩ :=
    orderSixtyFour_seven_defect_components_orthogonalArray_matching
      G hfree hmin hcover hcount
  have hrecip (i j : Fin 6) (x : (κ i).1.supp) :
      ℓ i (ℓ j x.1).1 = x := by
    have hadj : G.Adj (ℓ j x.1).1 x.1 := by
      exact (hiff j (ℓ j x.1) x.1).mpr rfl
    exact (hiff i x (ℓ j x.1).1).mp hadj.symm
  let m : ∀ i j : Fin 6, (κ i).1.supp ≃ (κ j).1.supp :=
    fun i j =>
      { toFun := fun x => ℓ j x.1
        invFun := fun y => ℓ i y.1
        left_inv := hrecip i j
        right_inv := hrecip j i }
  refine ⟨c, hc16, κ, ℓ, m, hpair, hiff, ?_, ?_, ?_⟩
  · intro i j x
    rfl
  · intro i j x
    exact hrecip i j x
  · intro i x
    exact (hdiag i).2 x

end

end Erdos85
