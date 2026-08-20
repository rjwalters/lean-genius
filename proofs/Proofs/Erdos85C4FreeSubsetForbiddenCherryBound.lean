import Proofs.Erdos85C4FreeSubsetCherryBound

/-! # C4-free cherry bounds with forbidden target pairs -/

open Finset SimpleGraph

namespace Erdos85

/-- If a family `F` of pairs in `S` is known to have no common graph
neighbor, those pairs can be removed from the ordinary C4-free cherry bound. -/
theorem sum_choose_card_neighbor_inter_le_choose_card_sub_forbidden
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (S : Finset V)
    (F : Finset (Finset V))
    (hF : F ⊆ S.powersetCard 2)
    (hforbid : ∀ T ∈ F, ∀ x : V, ¬ T ⊆ G.neighborFinset x) :
    (∑ x : V, ((G.neighborFinset x ∩ S).card).choose 2) ≤
      S.card.choose 2 - F.card := by
  classical
  let P : Finset (Σ _x : V, Finset V) :=
    Finset.univ.sigma fun x ↦ (G.neighborFinset x ∩ S).powersetCard 2
  let Q : Finset (Finset V) := S.powersetCard 2 \ F
  have hcardP : P.card =
      ∑ x : V, ((G.neighborFinset x ∩ S).card).choose 2 := by
    dsimp only [P]
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro x _
    simp
  have hcardQ : Q.card = S.card.choose 2 - F.card := by
    dsimp only [Q]
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hF]
    simp
  rw [← hcardP, ← hcardQ]
  apply Finset.card_le_card_of_injOn
    (fun p : (Σ _x : V, Finset V) ↦ p.2)
  · intro p hp
    rcases p with ⟨x, T⟩
    change ⟨x, T⟩ ∈ Finset.univ.sigma (fun x ↦
      (G.neighborFinset x ∩ S).powersetCard 2) at hp
    change T ∈ S.powersetCard 2 \ F
    have hp' := (Finset.mem_sigma.mp hp).2
    change T ∈ (G.neighborFinset x ∩ S).powersetCard 2 at hp'
    rw [Finset.mem_powersetCard] at hp'
    rw [Finset.mem_sdiff, Finset.mem_powersetCard]
    refine ⟨⟨hp'.1.trans Finset.inter_subset_right, hp'.2⟩, ?_⟩
    intro hTF
    exact hforbid T hTF x
      (hp'.1.trans Finset.inter_subset_left)
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
  Erdos85.sum_choose_card_neighbor_inter_le_choose_card_sub_forbidden
