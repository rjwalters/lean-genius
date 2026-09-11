import Proofs.Erdos85AttachedMovedBound
import Proofs.Erdos85OrderSevenFixedGraph

namespace Erdos85

/-- The attached-set incidence bound leaves only ambient order80 and
    exactly three fixed vertices in a nonidentity period-seven action. -/
theorem card_eighty_fixed_three_of_period_seven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hmin : 9 ≤ G.minDegree)
    (hcard : Fintype.card V = 78 ∨ Fintype.card V = 80)
    (τ : V → V) (hperiod : τ^[7] = id)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (hmoved : ∃ x, τ x ≠ x) :
    Fintype.card V = 80 ∧ Fintype.card ({v : V | τ v = v} : Set V) = 3 := by
  classical
  obtain ⟨hcases, hfixed⟩ := fixed_graph_of_period_seven_card_seventyEight_or_eighty
    G hfree hmin hcard τ hperiod hmap hmoved
  let F : Set V := {v : V | τ v = v}
  let M : Set V := {v : V | τ v ≠ v}
  have hpos : 0 < Fintype.card F := by
    rcases hcases with ⟨_, h⟩ | ⟨_, h | h⟩ <;> change Fintype.card F = _ at h <;> omega
  letI : Nonempty F := Fintype.card_pos_iff.mp hpos
  let u : F := Classical.choice inferInstance
  have hpair : ((G.induce F).neighborFinset u).card = 2 := hfixed u
  obtain ⟨v, w, hvw, hset⟩ := Finset.card_eq_two.mp hpair
  have huv : G.Adj u.val v.val := by
    have hmem : v ∈ (G.induce F).neighborFinset u := by rw [hset]; simp
    exact ((G.induce F).mem_neighborFinset u v).mp hmem
  have huw : G.Adj u.val w.val := by
    have hmem : w ∈ (G.induce F).neighborFinset u := by rw [hset]; simp
    exact ((G.induce F).mem_neighborFinset u w).mp hmem
  have hreg : ∀ x, G.degree x = 9 :=
    regular_of_minDegree_card_lt_nextMooreLayer G hfree (by norm_num) hmin (by omega)
  have hM := seventySeven_le_card_moved_of_fixed_neighbors G hfree hreg τ hperiod hmap
    hfixed u.property v.property w.property huv huw (fun h => hvw (Subtype.ext h))
  change 77 ≤ Fintype.card M at hM
  have hpart := Fintype.sum_subtype_add_sum_subtype (fun x => τ x = x) (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hpart
  change Fintype.card F + Fintype.card M = Fintype.card V at hpart
  change Fintype.card V = 80 ∧ Fintype.card F = 3
  rcases hcases with ⟨hN, hF⟩ | ⟨hN, hF | hF⟩
  all_goals
    change Fintype.card F = _ at hF
    omega

/-- At order78 a period-seven adjacency-preserving map is the identity. -/
theorem no_nonidentity_period_seven_of_card_seventyEight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hmin : 9 ≤ G.minDegree)
    (hcard : Fintype.card V = 78)
    (τ : V → V) (hperiod : τ^[7] = id)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y)) : τ = id := by
  classical
  by_contra hne
  have hmoved : ∃ x, τ x ≠ x := by
    by_contra h
    push Not at h
    exact hne (funext h)
  have h := (card_eighty_fixed_three_of_period_seven G hfree hmin (Or.inl hcard)
    τ hperiod hmap hmoved).1
  omega

end Erdos85
