import Proofs.Erdos85SevenRegularNearTwinCommutingGraphBalance

/-! # Canonical owner color distinguishing a defect near-twin pair -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- In the all-size-sixteen order-64 branch, a distinct nonadjacent near-twin
pair has a unique owner color on the pair.  For that very owner color, the
commuting-operator near-twin balance holds with a distinct private pair.

This packages the two ingredients needed for the selector-collision endgame:
the owner row difference is known to be nonzero (already at the opposite
endpoint), while its propagation is controlled exactly by the defect graph. -/
theorem orderSixtyFour_nearTwin_exists_distinguishingOwner_signed_balance
    (G : SimpleGraph (Fin 64)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 (Fin 64) G)
    (hreg : ∀ x, G.degree x = 8)
    (hcomponents : ∀ c : (secondOrderDefectGraph G).ConnectedComponent,
      c.supp.ncard = 16)
    {x y : Fin 64} (hxy : x ≠ y)
    (hnotD : ¬(secondOrderDefectGraph G).Adj x y)
    (hcommon : ((secondOrderDefectGraph G).neighborFinset x ∩
      (secondOrderDefectGraph G).neighborFinset y).card = 6) :
    ∃ c : (secondOrderDefectGraph G).ConnectedComponent,
      (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x y ∧
      ∃ p q : Fin 64, p ≠ q ∧ ∀ z : Fin 64,
        (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ p z -
            (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ q z =
          ∑ w : Fin 64,
            ((componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ x w -
              (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ y w) *
                (secondOrderDefectGraph G).adjMatrix ℤ w z := by
  obtain ⟨c, hcOwner, _hcUnique⟩ :=
    (not_secondOrderDefect_adj_iff_existsUnique_componentOwnerGraph_adj
      G hfree hxy).mp hnotD
  refine ⟨c, hcOwner, ?_⟩
  exact orderSixtyFour_nearTwin_ownerGraph_signed_balance
    G hfree hreg c (hcomponents c) hcommon

/-- The selected owner really distinguishes the two near-twin rows: at the
column `y`, the `x` row contains an edge and the `y` row contains no loop. -/
theorem componentOwnerGraph_adj_implies_rows_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (c : (secondOrderDefectGraph G).ConnectedComponent)
    {x y : V}
    (howner : (componentOwnerGraph G (secondOrderDefectGraph G) c).Adj x y) :
    ¬(∀ w : V,
      (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ x w =
      (componentOwnerGraph G (secondOrderDefectGraph G) c).adjMatrix ℤ y w) := by
  intro hrows
  have h := hrows y
  have hnloop : ¬(componentOwnerGraph G (secondOrderDefectGraph G) c).Adj y y :=
    (componentOwnerGraph G (secondOrderDefectGraph G) c).loopless.irrefl y
  simp only [SimpleGraph.adjMatrix_apply, howner, hnloop, if_true, if_false] at h
  omega

end

end Erdos85
