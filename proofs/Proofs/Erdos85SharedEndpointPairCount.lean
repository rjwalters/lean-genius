import Proofs.Erdos85EdgeIndexedServiceSharedEndpointForbiddenPairs

/-! # Counting shared-endpoint pairs in an internal edge family -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

set_option maxHeartbeats 800000 in
/-- If every vertex of `S` lies on exactly three type-two edges, then the
unordered pairs of type-two edges sharing an endpoint are counted exactly
three times per vertex. -/
theorem sharedEndpointShoreEdgePairFinset_card_eq_three_mul_card
    {V : Type*} [Fintype V] [DecidableEq V]
    (R : SimpleGraph V) [DecidableRel R.Adj] (S : Finset V)
    (hinc : ∀ x ∈ S,
      ((shoreTypeEdgeFinset R S 2).filter fun a ↦
        x ∈ a.1.toFinset).card = 3) :
    (sharedEndpointShoreEdgePairFinset R S).card = 3 * S.card := by
  classical
  let E := shoreTypeEdgeFinset R S 2
  let P : Finset (Σ _x : V, Finset R.edgeFinset) :=
    S.sigma fun x ↦ (E.filter fun a ↦ x ∈ a.1.toFinset).powersetCard 2
  let F := sharedEndpointShoreEdgePairFinset R S
  have hcardP : P.card = 3 * S.card := by
    dsimp only [P]
    rw [Finset.card_sigma]
    calc
      (∑ x ∈ S, ((E.filter fun a ↦ x ∈ a.1.toFinset).powersetCard 2).card) =
          ∑ _x ∈ S, 3 := by
            apply Finset.sum_congr rfl
            intro x hx
            have hc : (E.filter fun a ↦ x ∈ a.1.toFinset).card = 3 := by
              simpa [E] using hinc x hx
            rw [Finset.card_powersetCard, hc]
            norm_num [Nat.choose]
      _ = 3 * S.card := by simp [mul_comm]
  rw [← hcardP]
  symm
  change P.card = F.card
  refine Finset.card_bij (s := P) (t := F) (fun p _ ↦ p.2) ?_ ?_ ?_
  · intro p hp
    rcases p with ⟨x, T⟩
    dsimp only [P] at hp
    change T ∈ F
    have hp' := Finset.mem_sigma.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨?_, ⟨x, hp'.1, ?_⟩⟩
    · have hsub := (Finset.mem_powersetCard.mp hp'.2).1.trans
          (Finset.filter_subset (fun a ↦ x ∈ a.1.toFinset) E)
      apply Finset.mem_powersetCard.mpr
      exact ⟨by simpa [E] using hsub,
        (Finset.mem_powersetCard.mp hp'.2).2⟩
    · intro a ha
      exact (Finset.mem_filter.mp
        ((Finset.mem_powersetCard.mp hp'.2).1 ha)).2
  · intro p hp q hq hpq
    rcases p with ⟨x, T⟩
    rcases q with ⟨y, U⟩
    change T = U at hpq
    subst U
    have hp' : x ∈ S ∧
        T ∈ (E.filter fun a ↦ x ∈ a.1.toFinset).powersetCard 2 := by
      dsimp only [P] at hp
      exact Finset.mem_sigma.mp hp
    have hq' : y ∈ S ∧
        T ∈ (E.filter fun a ↦ y ∈ a.1.toFinset).powersetCard 2 := by
      dsimp only [P] at hq
      exact Finset.mem_sigma.mp hq
    have hxy : x = y := by
      by_contra hne
      obtain ⟨a, b, hab, hT⟩ := Finset.card_eq_two.mp
        (Finset.mem_powersetCard.mp hp'.2).2
      have hxa : x ∈ a.1.toFinset := by
        exact (Finset.mem_filter.mp
          ((Finset.mem_powersetCard.mp hp'.2).1 (hT ▸ by simp))).2
      have hxb : x ∈ b.1.toFinset := by
        exact (Finset.mem_filter.mp
          ((Finset.mem_powersetCard.mp hp'.2).1 (hT ▸ by simp))).2
      have hya : y ∈ a.1.toFinset := by
        exact (Finset.mem_filter.mp
          ((Finset.mem_powersetCard.mp hq'.2).1 (hT ▸ by simp))).2
      have hyb : y ∈ b.1.toFinset := by
        exact (Finset.mem_filter.mp
          ((Finset.mem_powersetCard.mp hq'.2).1 (hT ▸ by simp))).2
      have hpairCard : ({x, y} : Finset V).card = 2 := by simp [hne]
      have haCard : a.1.toFinset.card = 2 :=
        R.card_toFinset_mem_edgeFinset a
      have hbCard : b.1.toFinset.card = 2 :=
        R.card_toFinset_mem_edgeFinset b
      have haeq : a.1.toFinset = {x, y} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hxa
          · exact hya
        · rw [haCard, hpairCard]
      have hbeq : b.1.toFinset = {x, y} := by
        symm
        apply Finset.eq_of_subset_of_card_le
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hxb
          · exact hyb
        · rw [hbCard, hpairCard]
      apply hab
      apply Subtype.ext
      apply Sym2.ext
      intro z
      simpa only [Sym2.mem_toFinset] using
        (Finset.ext_iff.mp (haeq.trans hbeq.symm) z)
    subst y
    rfl
  · intro T hT
    change T ∈ F at hT
    obtain ⟨x, hxS, hx⟩ := (Finset.mem_filter.mp hT).2
    refine ⟨⟨x, T⟩, ?_, rfl⟩
    dsimp only [P]
    apply Finset.mem_sigma.mpr
    refine ⟨hxS, Finset.mem_powersetCard.mpr ⟨?_, ?_⟩⟩
    · intro a ha
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).1 ha,
          hx a ha⟩
    · exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hT).1).2

end

end Erdos85

#print axioms
  Erdos85.sharedEndpointShoreEdgePairFinset_card_eq_three_mul_card
