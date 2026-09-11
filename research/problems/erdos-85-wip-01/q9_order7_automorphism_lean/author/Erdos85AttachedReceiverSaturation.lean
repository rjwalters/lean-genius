import Proofs.Erdos85AttachedMovedBound

namespace Erdos85

/-- Equality at77 moved vertices forces every residual vertex to meet
    the attached set at the centre. -/
theorem exists_attached_neighbor_of_moved_card_seventySeven
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (hreg : ∀ x, G.degree x = 9)
    (τ : V → V) (hperiod : τ^[7] = id)
    (hmap : ∀ {x y}, G.Adj x y → G.Adj (τ x) (τ y))
    (hfixed : ∀ x : ({v : V | τ v = v} : Set V),
      (G.induce {v : V | τ v = v}).degree x = 2)
    (hMcard : Fintype.card ({x : V | τ x ≠ x} : Set V) = 77)
    {u v w : V} (hu : τ u = u) (hv : τ v = v) (hw : τ w = w)
    (huv : G.Adj u v) (huw : G.Adj u w) (hvw : v ≠ w)
    {x : V} (hxmoved : τ x ≠ x)
    (hxout : x ∉ movedNeighborFinset G τ u ∪ movedNeighborFinset G τ v ∪ movedNeighborFinset G τ w) :
    ∃ a ∈ movedNeighborFinset G τ u, G.Adj x a := by
  classical
  let A := movedNeighborFinset G τ u
  let B := movedNeighborFinset G τ v
  let C := movedNeighborFinset G τ w
  let M := Finset.univ.filter (fun x : V => τ x ≠ x)
  let T := A ∪ B ∪ C
  let D := M \ T
  have hA : A.card = 7 := card_movedNeighborFinset_eq_seven G τ u hu (hreg u) (hfixed ⟨u, hu⟩)
  have hB : B.card = 7 := card_movedNeighborFinset_eq_seven G τ v hv (hreg v) (hfixed ⟨v, hv⟩)
  have hC : C.card = 7 := card_movedNeighborFinset_eq_seven G τ w hw (hreg w) (hfixed ⟨w, hw⟩)
  have hAB : Disjoint A B := movedNeighborFinset_disjoint_of_fixed G hfree τ hmap hu hv (G.ne_of_adj huv)
  have hAC : Disjoint A C := movedNeighborFinset_disjoint_of_fixed G hfree τ hmap hu hw (G.ne_of_adj huw)
  have hBC : Disjoint B C := movedNeighborFinset_disjoint_of_fixed G hfree τ hmap hv hw hvw
  have hT : T.card = 21 := by
    dsimp [T]
    rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩),
      Finset.card_union_of_disjoint hAB, hA, hB, hC]
  have hTM : T ⊆ M := by
    intro x hx
    simp only [T, Finset.mem_union] at hx
    rcases hx with (hx | hx) | hx
    all_goals
      simp only [A, B, C, mem_movedNeighborFinset] at hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx.2⟩
  have hDM : D.card + 21 = M.card := by
    have h := Finset.card_sdiff_add_card_eq_card hTM
    simpa only [hT] using h
  let b : V → ℕ := fun x => (G.neighborFinset x ∩ A).card
  have hzero : ∀ x, x ≠ u → x ∉ D → b x = 0 := by
    intro x hxu hxD
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    obtain ⟨hxa, ha⟩ := Finset.mem_inter.mp ha
    have hxa := (G.mem_neighborFinset x a).mp hxa
    have ha' := (mem_movedNeighborFinset G τ u a).mp ha
    by_cases hxf : τ x = x
    · exact hxu (fixed_neighbors_eq_of_moved hfree τ hmap ha'.2 hxf hu hxa.symm ha'.1.symm)
    · have hxM : x ∈ M := Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxf⟩
      have hxT : x ∈ T := by
        by_contra h
        exact hxD (Finset.mem_sdiff.mpr ⟨hxM, h⟩)
      simp only [T, Finset.mem_union] at hxT
      rcases hxT with (hxA | hxB) | hxC
      · have hx' := (mem_movedNeighborFinset G τ u x).mp hxA
        exact not_adj_moved_neighbors_of_fixed_period_seven G hfree τ hperiod hmap
          u hu (hreg u) (hfixed ⟨u, hu⟩) hx'.1 ha'.1 hx'.2 ha'.2 hxa
      · exact not_adj_movedNeighborFinset_of_fixed_adj G hfree τ hu hv huv ha hxB hxa.symm
      · exact not_adj_movedNeighborFinset_of_fixed_adj G hfree τ hu hw huw ha hxC hxa.symm
  have hpoint : ∀ x : V, b x ≤ (if x = u then A.card else 0) + (if x ∈ D then 1 else 0) := by
    intro x
    by_cases hxu : x = u
    · have hle : b x ≤ A.card := Finset.card_le_card Finset.inter_subset_right
      simp only [if_pos hxu]
      omega
    · have hle : b x ≤ 1 := card_neighbor_inter_movedNeighborFinset_le_one G hfree τ hxu
      by_cases hxD : x ∈ D
      · simpa only [if_neg hxu, if_pos hxD, zero_add] using hle
      · rw [hzero x hxu hxD]
        exact Nat.zero_le _
  have hM : M.card = 77 := by
    have heq : M = ({x : V | τ x ≠ x} : Set V).toFinset := by ext x; simp [M]
    rw [heq, Set.toFinset_card, hMcard]
  have hD : D.card = 56 := by omega
  have htotal : (∑ x : V, b x) = 63 := by
    rw [show (∑ x : V, b x) = ∑ a ∈ A, G.degree a from sum_card_neighbor_inter_eq_sum_degree G A]
    simp [hreg, hA]
  have hsumEq : (∑ x : V, b x) =
      ∑ x : V, ((if x = u then A.card else 0) + (if x ∈ D then 1 else 0)) := by
    simp [Finset.sum_add_distrib, htotal, hA, hD]
  have hall := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ) (fun z _ => hpoint z)).mp hsumEq
  have hxD : x ∈ D := Finset.mem_sdiff.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxmoved⟩, hxout⟩
  have hxu : x ≠ u := by intro h; subst x; exact hxmoved hu
  have hbx : b x = 1 := by
    simpa only [if_neg hxu, if_pos hxD, zero_add] using hall x (Finset.mem_univ x)
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < (G.neighborFinset x ∩ A).card by change 0 < b x; rw [hbx]; decide)
  exact ⟨a, (Finset.mem_inter.mp ha).2, (G.mem_neighborFinset x a).mp (Finset.mem_inter.mp ha).1⟩

end Erdos85
