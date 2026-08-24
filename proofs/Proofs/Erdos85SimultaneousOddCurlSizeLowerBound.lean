import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Ring.Parity

/-!
# Size lower bound for a simultaneous odd curl

The two cycle projections of the final `00` holonomy use the same port set
but have disjoint edge sets by C4-freeness.  On three ports both cycles would
exhaust the same three-edge universe, so the first possible odd size is five.
-/

namespace Erdos85

/-- Two three-edge spanning factors of a three-edge universe cannot be
edge-disjoint. -/
theorem not_disjoint_of_three_edge_subsets
    {E : Type*} [DecidableEq E]
    (U A B : Finset E)
    (hU : U.card = 3)
    (hA : A.card = 3) (hB : B.card = 3)
    (hAU : A ⊆ U) (hBU : B ⊆ U) :
    ¬ Disjoint A B := by
  intro hdis
  have hAe : A = U :=
    Finset.eq_of_subset_of_card_le hAU (by omega)
  have hBe : B = U :=
    Finset.eq_of_subset_of_card_le hBU (by omega)
  rw [hAe, hBe] at hdis
  have hpos : 0 < U.card := by omega
  obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
  exact Finset.disjoint_left.mp hdis he he

/-- An odd cycle size at least three, once the three-cycle simultaneous
branch is excluded, is at least five. -/
theorem five_le_of_odd_three_le_ne_three
    (n : ℕ) (hodd : Odd n) (hthree : 3 ≤ n) (hne : n ≠ 3) :
    5 ≤ n := by
  rcases hodd with ⟨k, hk⟩
  omega

/-- **Simultaneous-curl lower bound (`73rnz_cjibkzzx--y`).**  If a
three-port curl would give two disjoint three-edge projections in the common
three-edge universe, that case is impossible; hence every odd curl of cycle
size at least three has size at least five. -/
theorem simultaneousOddCurl_five_le
    {E : Type*} [DecidableEq E]
    (n : ℕ) (hodd : Odd n) (hthree : 3 ≤ n)
    (U A B : Finset E)
    (hthreeModel : n = 3 →
      U.card = 3 ∧ A.card = 3 ∧ B.card = 3 ∧
        A ⊆ U ∧ B ⊆ U ∧ Disjoint A B) :
    5 ≤ n := by
  apply five_le_of_odd_three_le_ne_three n hodd hthree
  intro hn
  obtain ⟨hU, hA, hB, hAU, hBU, hdis⟩ := hthreeModel hn
  exact not_disjoint_of_three_edge_subsets U A B hU hA hB hAU hBU hdis

end Erdos85

#print axioms Erdos85.not_disjoint_of_three_edge_subsets
#print axioms Erdos85.five_le_of_odd_three_le_ne_three
#print axioms Erdos85.simultaneousOddCurl_five_le
