import Proofs.Erdos85GadgetCounting

namespace Erdos85

/-- All two-step walks from a vertex into a set avoiding it have distinct
endpoints in a C4-free graph. -/
theorem sum_two_step_endpoints_le_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (a : V) (B : Finset V) (ha : a ∉ B) :
    (∑ u ∈ G.neighborFinset a, (G.neighborFinset u ∩ B).card) ≤ B.card := by
  classical
  have hf (b : V) :
      (G.neighborFinset a).filter (fun u => b ∈ G.neighborFinset u ∩ B) =
        if b ∈ B then G.neighborFinset a ∩ G.neighborFinset b else ∅ := by
    by_cases hb : b ∈ B
    · simp only [if_pos hb]
      ext u
      simp [hb, G.adj_comm]
    · simp [hb]
  have hp (b : V) :
      ((G.neighborFinset a).filter (fun u => b ∈ G.neighborFinset u ∩ B)).card ≤
        if b ∈ B then 1 else 0 := by
    rw [hf]
    split_ifs with hb
    · apply card_inter_neighborFinset_le_one hfree
      intro h
      exact ha (h.symm ▸ hb)
    · simp
  have h := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hp b)
  rw [sum_card_filter_mem_eq_sum_card] at h
  simpa using h

/-- More two-step walks than possible endpoints force a C4. -/
theorem containsC4_of_two_step_count_gt_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (B : Finset V) (ha : a ∉ B)
    (hcount : B.card < ∑ u ∈ G.neighborFinset a, (G.neighborFinset u ∩ B).card) :
    containsC4 V G := by
  by_contra hfree
  exact (Nat.not_le_of_lt hcount) (sum_two_step_endpoints_le_card G hfree a B ha)

end Erdos85
