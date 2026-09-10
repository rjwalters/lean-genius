import Proofs.Erdos85SaturatedNeighborBijection

/-! A cross matching deficient by one has one omitted endpoint on each side. -/
namespace Erdos85
open SimpleGraph
noncomputable section

private theorem unmatched_count_eq_one
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hle : ∀ x ∈ A, (G.neighborFinset x ∩ B).card ≤ 1)
    (hmass : (∑ x ∈ A, (G.neighborFinset x ∩ B).card) + 1 = A.card) :
    (A.filter fun x => (G.neighborFinset x ∩ B).card = 0).card = 1 := by
  classical
  have hs : (∑ x ∈ A, ((G.neighborFinset x ∩ B).card +
      if (G.neighborFinset x ∩ B).card = 0 then 1 else 0)) = ∑ _x ∈ A, 1 := by
    apply Finset.sum_congr rfl
    intro x hx
    have hc := hle x hx
    split_ifs <;> omega
  rw [Finset.sum_add_distrib, ← Finset.card_filter] at hs
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at hs
  omega

theorem deficient_neighbor_blocks_equiv
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A B : Finset V)
    (hcard : A.card = B.card)
    (hA : ∀ x ∈ A, (G.neighborFinset x ∩ B).card ≤ 1)
    (hB : ∀ y ∈ B, (G.neighborFinset y ∩ A).card ≤ 1)
    (hmass : (∑ x ∈ A, (G.neighborFinset x ∩ B).card) + 1 = A.card) :
    ∃ a ∈ A, ∃ b ∈ B,
      (∀ x ∈ A, (G.neighborFinset x ∩ B).card = 0 ↔ x = a) ∧
      (∀ y ∈ B, (G.neighborFinset y ∩ A).card = 0 ↔ y = b) ∧
      ∃ e : (↑(A.erase a) : Set V) ≃ (↑(B.erase b) : Set V),
        ∀ (x : (↑(A.erase a) : Set V)) (y : (↑(B.erase b) : Set V)),
          G.Adj x.val y.val ↔ e x = y := by
  classical
  have hmB : (∑ y ∈ B, (G.neighborFinset y ∩ A).card) + 1 = B.card := by
    rw [← sum_card_neighbor_inter_comm G A B, ← hcard]
    exact hmass
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (unmatched_count_eq_one G A B hA hmass)
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp (unmatched_count_eq_one G B A hB hmB)
  have haF : a ∈ A.filter fun x => (G.neighborFinset x ∩ B).card = 0 := by rw [ha]; simp
  have hbF : b ∈ B.filter fun y => (G.neighborFinset y ∩ A).card = 0 := by rw [hb]; simp
  have haA := (Finset.mem_filter.mp haF).1
  have hbB := (Finset.mem_filter.mp hbF).1
  have ha0 := (Finset.mem_filter.mp haF).2
  have hb0 := (Finset.mem_filter.mp hbF).2
  refine ⟨a, haA, b, hbB, ?_, ?_, ?_⟩
  · intro x hx
    have he : x ∈ A.filter (fun x => (G.neighborFinset x ∩ B).card = 0) ↔ x = a := by
      rw [ha, Finset.mem_singleton]
    simpa only [Finset.mem_filter, hx, true_and] using he
  · intro y hy
    have he : y ∈ B.filter (fun y => (G.neighborFinset y ∩ A).card = 0) ↔ y = b := by
      rw [hb, Finset.mem_singleton]
    simpa only [Finset.mem_filter, hy, true_and] using he
  have hno (x : V) (hx : x ∈ A) : ¬ G.Adj x b := by
    intro hxb
    have hm : x ∈ G.neighborFinset b ∩ A :=
      Finset.mem_inter.mpr ⟨(G.mem_neighborFinset b x).mpr hxb.symm, hx⟩
    rw [Finset.card_eq_zero.mp hb0] at hm
    exact Finset.notMem_empty _ hm
  have hinter (x : V) (hx : x ∈ A) :
      G.neighborFinset x ∩ B.erase b = G.neighborFinset x ∩ B := by
    ext y
    have hn := hno x hx
    simp only [Finset.mem_inter, Finset.mem_erase, SimpleGraph.mem_neighborFinset]
    aesop
  have hAc := Finset.card_erase_of_mem haA
  have hBc := Finset.card_erase_of_mem hbB
  have hmassE : (∑ x ∈ A.erase a, (G.neighborFinset x ∩ B.erase b).card) = (A.erase a).card := by
    have hs := Finset.sum_erase_add A (fun x => (G.neighborFinset x ∩ B).card) haA
    rw [ha0, Nat.add_zero] at hs
    have he : (∑ x ∈ A.erase a, (G.neighborFinset x ∩ B.erase b).card) =
        ∑ x ∈ A.erase a, (G.neighborFinset x ∩ B).card :=
      Finset.sum_congr rfl (fun x hx => congrArg Finset.card (hinter x (Finset.mem_of_mem_erase hx)))
    rw [he, hs, hAc]
    omega
  apply saturated_neighbor_blocks_equiv G (A.erase a) (B.erase b) (by omega) ?_ ?_ hmassE
  · intro x hx
    rw [hinter x (Finset.mem_of_mem_erase hx)]
    exact hA x (Finset.mem_of_mem_erase hx)
  · intro y hy
    exact (Finset.card_le_card (Finset.inter_subset_inter_left (Finset.erase_subset a A))).trans
      (hB y (Finset.mem_of_mem_erase hy))

end
end Erdos85
#print axioms Erdos85.deficient_neighbor_blocks_equiv
