import Proofs.Erdos85BinarySquareCenterGridOperator

/-! # Two forced owner-colored blocks from an order-64 defect near-twin -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the four-component order-64 branch, a defect near-twin pair forces at
least two distinct nonexceptional component-selector blocks.  Every cross pair
in either block belongs to exactly one component owner graph. -/
theorem orderSixtyFour_fourComponents_nearTwin_exists_two_uniqueOwnerBlocks
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcount : Fintype.card
      (secondOrderDefectGraph G).ConnectedComponent = 4)
    {x y : Fin 64} (hxy : x ≠ y)
    (hnotD : ¬ (secondOrderDefectGraph G).Adj x y)
    (hcodegree : ((secondOrderDefectGraph G).adjMatrix ℤ *
      (secondOrderDefectGraph G).adjMatrix ℤ) x y = 6) :
    ∃ p : Fin 64 × Fin 64, ∃ w : Fin 64,
      ∃ k₁ k₂ : (secondOrderDefectGraph G).ConnectedComponent,
        p ∈ crossRootDefectCenterPairs G x y ∧
        w ∈ G.neighborFinset x ∩ G.neighborFinset y ∧
        k₁ ≠ k₂ ∧
        ∀ k : (secondOrderDefectGraph G).ConnectedComponent,
          k = k₁ ∨ k = k₂ →
          ∀ u ∈ componentNeighborFinset G (secondOrderDefectGraph G) k x,
            ∀ v ∈ componentNeighborFinset G (secondOrderDefectGraph G) k y,
              ∃! c : (secondOrderDefectGraph G).ConnectedComponent,
                (componentOwnerGraph G
                  (secondOrderDefectGraph G) c).Adj u v := by
  classical
  obtain ⟨p, w, hp, hw, hall⟩ :=
    orderSixtyFour_nearTwin_otherComponents_unique_owner_blocks
      G hfree hreg hxy hnotD hcodegree
  let D := secondOrderDefectGraph G
  let bridge : D.ConnectedComponent := D.connectedComponentMk p.1
  let common : D.ConnectedComponent := D.connectedComponentMk w
  let S : Finset D.ConnectedComponent :=
    ((Finset.univ.erase bridge).erase common)
  have hcountD : Fintype.card D.ConnectedComponent = 4 := by
    simpa [D] using hcount
  have hScard : 2 ≤ S.card := by
    change 2 ≤ ((Finset.univ.erase bridge).erase common).card
    by_cases hbc : bridge = common
    · rw [← hbc, Finset.erase_idem,
        Finset.card_erase_of_mem (Finset.mem_univ bridge),
        Finset.card_univ, hcountD]
      norm_num
    · have hcMem : common ∈ (Finset.univ : Finset D.ConnectedComponent).erase bridge :=
        Finset.mem_erase.mpr ⟨Ne.symm hbc, Finset.mem_univ common⟩
      rw [Finset.card_erase_of_mem hcMem,
        Finset.card_erase_of_mem (Finset.mem_univ bridge),
        Finset.card_univ, hcountD]
  obtain ⟨k₁, hk₁S, k₂, hk₂S, hk₁k₂⟩ :=
    Finset.one_lt_card.mp (show 1 < S.card by omega)
  have hk₁Common : k₁ ≠ common := (Finset.mem_erase.mp hk₁S).1
  have hk₁Bridge : k₁ ≠ bridge :=
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase hk₁S)).1
  have hk₂Common : k₂ ≠ common := (Finset.mem_erase.mp hk₂S).1
  have hk₂Bridge : k₂ ≠ bridge :=
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase hk₂S)).1
  refine ⟨p, w, k₁, k₂, hp, hw, hk₁k₂, ?_⟩
  intro k hk
  rcases hk with hk | hk
  · subst k
    exact hall k₁ hk₁Bridge hk₁Common
  · subst k
    exact hall k₂ hk₂Bridge hk₂Common

end

end Erdos85
