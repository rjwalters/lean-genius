import Proofs.Erdos85Problem

/-! # Cherry bounds into a chosen vertex subset of a C4-free graph -/

open Finset SimpleGraph

namespace Erdos85

/-- A C4-free graph has at most one center for every pair in `S`.  Equivalently,
the total number of unordered pairs of `S`-neighbors over all centers is at
most `choose(|S|,2)`. -/
theorem sum_choose_card_neighbor_inter_le_choose_card_of_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (S : Finset V) :
    (∑ x : V, ((G.neighborFinset x ∩ S).card).choose 2) ≤
      S.card.choose 2 := by
  classical
  let P : Finset (Σ _x : V, Finset V) :=
    Finset.univ.sigma fun x ↦ (G.neighborFinset x ∩ S).powersetCard 2
  let Q : Finset (Finset V) := S.powersetCard 2
  have hcardP : P.card =
      ∑ x : V, ((G.neighborFinset x ∩ S).card).choose 2 := by
    dsimp only [P]
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro x _
    simp
  have hcardQ : Q.card = S.card.choose 2 := by simp [Q]
  rw [← hcardP, ← hcardQ]
  apply Finset.card_le_card_of_injOn
    (fun p : (Σ _x : V, Finset V) ↦ p.2)
  · intro p hp
    rcases p with ⟨x, T⟩
    change ⟨x, T⟩ ∈ P at hp
    change T ∈ Q
    change ⟨x, T⟩ ∈ Finset.univ.sigma (fun x ↦
      (G.neighborFinset x ∩ S).powersetCard 2) at hp
    change T ∈ S.powersetCard 2
    have hp' := (Finset.mem_sigma.mp hp).2
    rw [Finset.mem_powersetCard] at hp' ⊢
    exact ⟨hp'.1.trans Finset.inter_subset_right, hp'.2⟩
  · intro p hp q hq hpq
    rcases p with ⟨x, T⟩
    rcases q with ⟨y, U⟩
    change T = U at hpq
    subst U
    have hxyEq : x = y := by
      by_contra hxy
      change ⟨x, T⟩ ∈ Finset.univ.sigma (fun x ↦
        (G.neighborFinset x ∩ S).powersetCard 2) at hp
      change ⟨y, T⟩ ∈ Finset.univ.sigma (fun x ↦
        (G.neighborFinset x ∩ S).powersetCard 2) at hq
      have hp' : T ⊆ G.neighborFinset x ∩ S ∧ T.card = 2 := by
        simpa only [Finset.mem_powersetCard] using (Finset.mem_sigma.mp hp).2
      have hq' : T ⊆ G.neighborFinset y ∩ S ∧ T.card = 2 := by
        simpa only [Finset.mem_powersetCard] using (Finset.mem_sigma.mp hq).2
      have hsub : T ⊆ G.neighborFinset x ∩ G.neighborFinset y := by
        intro z hz
        exact Finset.mem_inter.mpr
          ⟨(Finset.mem_inter.mp (hp'.1 hz)).1,
            (Finset.mem_inter.mp (hq'.1 hz)).1⟩
      have hle := Finset.card_le_card hsub
      have hone := common_le_one_of_not_containsC4 hfree x y hxy
      omega
    subst y
    rfl

end Erdos85

#print axioms
  Erdos85.sum_choose_card_neighbor_inter_le_choose_card_of_not_containsC4
