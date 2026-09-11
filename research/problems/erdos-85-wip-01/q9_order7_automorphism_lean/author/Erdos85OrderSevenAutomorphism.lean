import Proofs.Erdos85OrderSevenSmallFixedSet
import Proofs.Erdos85AttachedReceiverSaturation
import Proofs.Erdos85NeighborCover

namespace Erdos85

/-- At order78 or80, every period-seven adjacency-preserving map of a
    C4-free minimum-degree-nine graph is the identity. -/
theorem no_nonidentity_period_seven_of_card_seventyEight_or_eighty
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hmin : 9 ≤ G.minDegree)
    (hcard : Fintype.card V = 78 ∨ Fintype.card V = 80)
    (τ : V → V) (hperiod : τ^[7] = id)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y)) : τ = id := by
  classical
  by_contra hne
  have hmoved : ∃ x, τ x ≠ x := by
    by_contra h
    push Not at h
    exact hne (funext h)
  obtain ⟨hN, hF⟩ := card_eighty_fixed_three_of_period_seven G hfree hmin hcard τ hperiod hmap hmoved
  have hfixed := (fixed_graph_of_period_seven_card_seventyEight_or_eighty
    G hfree hmin hcard τ hperiod hmap hmoved).2
  have hreg : ∀ x, G.degree x = 9 :=
    regular_of_minDegree_card_lt_nextMooreLayer G hfree (by norm_num) hmin (by omega)
  let F : Set V := {x : V | τ x = x}
  let M : Set V := {x : V | τ x ≠ x}
  change Fintype.card F = 3 at hF
  have hpart := Fintype.sum_subtype_add_sum_subtype (fun x => τ x = x) (fun _ => (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hpart
  change Fintype.card F + Fintype.card M = Fintype.card V at hpart
  have hM : Fintype.card M = 77 := by omega
  letI : Nonempty F := Fintype.card_pos_iff.mp (by omega)
  let u : F := Classical.choice inferInstance
  have hpair : ((G.induce F).neighborFinset u).card = 2 := hfixed u
  obtain ⟨v, w, hvw, hset⟩ := Finset.card_eq_two.mp hpair
  have huv : G.Adj u.val v.val := by
    have hmem : v ∈ (G.induce F).neighborFinset u := by rw [hset]; simp
    exact ((G.induce F).mem_neighborFinset u v).mp hmem
  have huw : G.Adj u.val w.val := by
    have hmem : w ∈ (G.induce F).neighborFinset u := by rw [hset]; simp
    exact ((G.induce F).mem_neighborFinset u w).mp hmem
  have huvne : u ≠ v := by intro h; have := G.ne_of_adj huv; exact this (congrArg Subtype.val h)
  have huwne : u ≠ w := by intro h; have := G.ne_of_adj huw; exact this (congrArg Subtype.val h)
  have hall : ∀ z : F, z = u ∨ z = v ∨ z = w := by
    have heq : ({u, v, w} : Finset F) = Finset.univ := by
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simp [hF, huvne, huwne, hvw]
    intro z
    have hz : z ∈ ({u, v, w} : Finset F) := by rw [heq]; exact Finset.mem_univ z
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hz
  have hvwadj : G.Adj v.val w.val := by
    have htwo : 1 < ((G.induce F).neighborFinset v).card := by
      change 1 < (G.induce F).degree v
      rw [hfixed v]
      decide
    obtain ⟨z, hz, hzu⟩ := Finset.exists_mem_ne htwo u
    have hvz := ((G.induce F).mem_neighborFinset v z).mp hz
    rcases hall z with h | h | h
    · exact False.elim (hzu h)
    · subst z
      exact False.elim (G.irrefl hvz)
    · subst z
      exact hvz
  let A := movedNeighborFinset G τ u.val
  let B := movedNeighborFinset G τ v.val
  let C := movedNeighborFinset G τ w.val
  have hA : A.card = 7 := card_movedNeighborFinset_eq_seven G τ u.val u.property (hreg _) (hfixed u)
  have hB : B.card = 7 := card_movedNeighborFinset_eq_seven G τ v.val v.property (hreg _) (hfixed v)
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < A.card by omega)
  have ha' := (mem_movedNeighborFinset G τ u.val a).mp ha
  let E := insert v.val B
  have hvB : v.val ∉ B := by simp [B]
  have hE : E.card = 8 := by rw [Finset.card_insert_of_notMem hvB, hB]
  have haE : a ∉ E := by
    intro h
    rcases Finset.mem_insert.mp h with h | h
    · subst a
      exact ha'.2 v.property
    · have hd := movedNeighborFinset_disjoint_of_fixed G hfree τ hmap u.property v.property (G.ne_of_adj huv)
      exact Finset.disjoint_left.mp hd ha h
  have hcover : ∀ z, G.Adj a z → ∃ b ∈ E, G.Adj z b := by
    intro z haz
    by_cases hzu : z = u.val
    · subst z
      exact ⟨v.val, Finset.mem_insert_self _ _, huv⟩
    · have hzmoved : τ z ≠ z := by
        intro hz
        exact hzu (fixed_neighbors_eq_of_moved hfree τ hmap ha'.2 hz u.property haz ha'.1.symm)
      have hzout : z ∉ A ∪ B ∪ C := by
        intro h
        rcases Finset.mem_union.mp h with h | hC
        · rcases Finset.mem_union.mp h with hA | hB
          · have hz' := (mem_movedNeighborFinset G τ u.val z).mp hA
            exact not_adj_moved_neighbors_of_fixed_period_seven G hfree τ hperiod hmap
              u.val u.property (hreg _) (hfixed u) ha'.1 hz'.1 ha'.2 hz'.2 haz
          · exact not_adj_movedNeighborFinset_of_fixed_adj G hfree τ u.property v.property huv ha hB haz
        · exact not_adj_movedNeighborFinset_of_fixed_adj G hfree τ u.property w.property huw ha hC haz
      have hzout' : z ∉ B ∪ A ∪ C := by simpa only [Finset.union_comm] using hzout
      obtain ⟨b, hb, hzb⟩ := exists_attached_neighbor_of_moved_card_seventySeven G hfree hreg τ hperiod hmap
        hfixed hM v.property u.property w.property huv.symm hvwadj (G.ne_of_adj huw) hzmoved hzout'
      exact ⟨b, Finset.mem_insert_of_mem hb, hzb⟩
  exact hfree (containsC4_of_neighbor_cover_card_lt_degree G a E haE hcover (by rw [hE, hreg]; decide))

end Erdos85
