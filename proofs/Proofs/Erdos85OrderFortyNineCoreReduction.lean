import Proofs.Erdos85OrderFortyNineNineHighContradiction
import Proofs.Erdos85OddComponentCount

/-!
# Plateau-core reduction at order 49

This joins the order-49 incidence census and checked nine-high terminal to
the plateau-core interface.  A hypothetical core has a connected normalized
representative whose degree-eight sector has size `1`, `3`, `5`, or `7`.
-/

namespace Erdos85

open SimpleGraph

/-- The exact surviving order-49 branches after the checked nine-high
contradiction. -/
theorem C4PlateauCore.exists_orderFortyNine_connected_fourHighBranches
    (hcore : C4PlateauCore 49 7) :
    ∃ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj),
      G.minDegree = 7 ∧ ¬ containsC4 (Fin 49) G ∧
      Fintype.card G.ConnectedComponent = 1 ∧
      ((orderFortyNineHighVertices G).card = 1 ∨
        (orderFortyNineHighVertices G).card = 3 ∨
        (orderFortyNineHighVertices G).card = 5 ∨
        (orderFortyNineHighVertices G).card = 7) := by
  rcases hcore with ⟨G, hdec, hmin, hfree, _hcover, _hnext⟩
  letI : DecidableRel G.Adj := hdec
  letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
  have hdegree : ∀ x : Fin 49, 7 ≤ G.degree x := fun x ↦
    hmin.ge.trans (G.minDegree_le_degree x)
  have hcount :=
    orderFortyNine_card_high_eq_one_or_three_or_five_or_seven_or_nine
      G hfree hdegree (by norm_num)
  have hconnected : Fintype.card G.ConnectedComponent = 1 := by
    have hmass := connectedComponent_count_mul_oddMoore_le_card
      G hfree (d := 7) (by norm_num) (by norm_num) hmin.ge
    have hkpos : 0 < Fintype.card G.ConnectedComponent := by
      rw [Fintype.card_pos_iff]
      exact ⟨G.connectedComponentMk ⟨0, by norm_num⟩⟩
    norm_num at hmass
    omega
  refine ⟨G, hdec, hmin, hfree, hconnected, ?_⟩
  rcases hcount with h1 | h3 | h5 | h7 | h9
  · exact Or.inl h1
  · exact Or.inr (Or.inl h3)
  · exact Or.inr (Or.inr (Or.inl h5))
  · exact Or.inr (Or.inr (Or.inr h7))
  · exact (false_of_orderFortyNine_nine_high
      G hfree hdegree (by norm_num) h9).elim

end Erdos85
