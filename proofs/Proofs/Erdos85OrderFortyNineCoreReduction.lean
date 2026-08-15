import Proofs.Erdos85OrderFortyNineNineHighContradiction
import Proofs.Erdos85OddComponentCount
import Proofs.Erdos85OrderFortyNineOneThreeHighProfile
import Proofs.Erdos85OrderFortyNineFiveHighTripleBound
import Proofs.Erdos85OrderFortyNineSevenHighProfile

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

/-- Fully numerical incidence profiles for the four surviving order-49
branches.  This is the direct input expected by a branch-specific terminal
or checked SAT reduction. -/
theorem C4PlateauCore.exists_orderFortyNine_surviving_incidence_profile
    (hcore : C4PlateauCore 49 7) :
    ∃ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj),
      G.minDegree = 7 ∧ ¬ containsC4 (Fin 49) G ∧
      Fintype.card G.ConnectedComponent = 1 ∧
      let H := orderFortyNineHighVertices G
      let n := orderFortyNineHighIncidenceCount G
      (H.card = 1 ∧ n 0 = 40 ∧ n 1 = 8 ∧ n 2 = 0 ∧ n 3 = 0) ∨
      (H.card = 3 ∧
        ((n 0 = 25 ∧ n 1 = 18 ∧ n 2 = 3 ∧ n 3 = 0) ∨
         (n 0 = 24 ∧ n 1 = 21 ∧ n 2 = 0 ∧ n 3 = 1))) ∨
      (H.card = 5 ∧
        ((n 0 = 14 ∧ n 1 = 20 ∧ n 2 = 10 ∧ n 3 = 0) ∨
         (n 0 = 13 ∧ n 1 = 23 ∧ n 2 = 7 ∧ n 3 = 1) ∨
         (n 0 = 12 ∧ n 1 = 26 ∧ n 2 = 4 ∧ n 3 = 2))) ∨
      (H.card = 7 ∧
        ((n 0 = 7 ∧ n 1 = 14 ∧ n 2 = 21 ∧ n 3 = 0) ∨
         (n 0 = 6 ∧ n 1 = 17 ∧ n 2 = 18 ∧ n 3 = 1) ∨
         (n 0 = 5 ∧ n 1 = 20 ∧ n 2 = 15 ∧ n 3 = 2) ∨
         (n 0 = 4 ∧ n 1 = 23 ∧ n 2 = 12 ∧ n 3 = 3) ∨
         (n 0 = 3 ∧ n 1 = 26 ∧ n 2 = 9 ∧ n 3 = 4) ∨
         (n 0 = 2 ∧ n 1 = 29 ∧ n 2 = 6 ∧ n 3 = 5) ∨
         (n 0 = 1 ∧ n 1 = 32 ∧ n 2 = 3 ∧ n 3 = 6) ∨
         (n 0 = 0 ∧ n 1 = 35 ∧ n 2 = 0 ∧ n 3 = 7))) := by
  obtain ⟨G, hdec, hmin, hfree, hconnected, hbranches⟩ :=
    hcore.exists_orderFortyNine_connected_fourHighBranches
  letI : DecidableRel G.Adj := hdec
  letI : DecidableRel (antipodalGraph G).Adj := Classical.decRel _
  letI : DecidableRel (triangleFreeEdgeGraph G).Adj := Classical.decRel _
  have hdegree : ∀ x : Fin 49, 7 ≤ G.degree x := fun x ↦
    hmin.ge.trans (G.minDegree_le_degree x)
  refine ⟨G, hdec, hmin, hfree, hconnected, ?_⟩
  dsimp only
  rcases hbranches with h1 | h3 | h5 | h7
  · left
    exact ⟨h1, orderFortyNine_highIncidence_profile_of_one_high
      G hfree hdegree (by norm_num) h1⟩
  · right; left
    exact ⟨h3, orderFortyNine_highIncidence_profile_of_three_high
      G hfree hdegree (by norm_num) h3⟩
  · right; right; left
    exact ⟨h5, orderFortyNine_highIncidence_profile_of_five_high
      G hfree hdegree (by norm_num) h5⟩
  · right; right; right
    exact ⟨h7, orderFortyNine_highIncidence_profiles_of_seven_high
      G hfree hdegree (by norm_num) h7⟩

end Erdos85
