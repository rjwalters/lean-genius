import Proofs.Erdos85OrderSixtyFourOrthogonalArray

/-! # Matching-compatible order-64 orthogonal array -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The coherent six-column orthogonal array remembers all adjacency to the
six small blocks.  On each block's own rows its label map is simultaneously
a fixed-point-free involution, namely that block's internal matching. -/
theorem orderSixtyFour_seven_defect_components_orthogonalArray_matching
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
          (∀ i (x : (κ i).1.supp) z, G.Adj x.1 z ↔ ℓ i z = x) ∧
          ∀ i,
            Function.Involutive (fun x : (κ i).1.supp => ℓ i x.1) ∧
            ∀ x : (κ i).1.supp, ℓ i x.1 ≠ x := by
  classical
  let D := secondOrderDefectGraph G
  obtain ⟨c, hc16, κ, ℓ, hℓadj, hpair⟩ :=
    orderSixtyFour_seven_defect_components_orthogonalArray
      G hfree hmin hcover hcount
  obtain ⟨c', hc'16, _hH, hsmall'⟩ :=
    orderSixtyFour_seven_defect_components_global_block_degrees
      G hfree hmin hcover hcount
  have hcc' : c = c' := by
    by_contra hne
    have hc8 := (hsmall' c hne).1
    omega
  have hsmall (k : D.ConnectedComponent) (hkc : k ≠ c) (z : Fin 64) :
      (componentNeighborFinset G D k z).card = 1 := by
    exact (hsmall' k (by simpa [hcc'] using hkc)).2 z
  have hiff (i : Fin 6) (x : (κ i).1.supp) (z : Fin 64) :
      G.Adj x.1 z ↔ ℓ i z = x := by
    constructor
    · intro hx
      let S := componentNeighborFinset G D (κ i).1 z
      have hxS : x.1 ∈ S := by
        apply Finset.mem_filter.mpr
        refine ⟨(G.mem_neighborFinset z x.1).mpr hx.symm, ?_⟩
        exact (ConnectedComponent.mem_supp_iff (κ i).1 x.1).mp x.2
      have hℓS : (ℓ i z).1 ∈ S := by
        apply Finset.mem_filter.mpr
        refine ⟨(G.mem_neighborFinset z (ℓ i z).1).mpr (hℓadj i z).symm, ?_⟩
        exact (ConnectedComponent.mem_supp_iff (κ i).1 (ℓ i z).1).mp
          (ℓ i z).2
      obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (hsmall (κ i).1 (κ i).2 z)
      change x.1 ∈ componentNeighborFinset G D (κ i).1 z at hxS
      change (ℓ i z).1 ∈ componentNeighborFinset G D (κ i).1 z at hℓS
      rw [ha] at hxS hℓS
      apply Subtype.ext
      have hxval : x.1 = a := by simpa using hxS
      have hℓval : (ℓ i z).1 = a := by simpa using hℓS
      exact hℓval.trans hxval.symm
    · intro h
      simpa [h] using hℓadj i z
  refine ⟨c, hc16, κ, ℓ, hpair, hiff, ?_⟩
  intro i
  constructor
  · intro x
    have hx : G.Adj (ℓ i x.1).1 x.1 := hℓadj i x.1
    exact (hiff i x (ℓ i x.1).1).mp hx.symm
  · intro x hfix
    have hloop : G.Adj x.1 x.1 := by
      simpa [hfix] using hℓadj i x.1
    exact G.loopless.irrefl x.1 hloop

end

end Erdos85
