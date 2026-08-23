import Proofs.Erdos85OddSquareOrderNineNearRegularConnectivityTerminal

/-! # Generic graph bridges for a deleted-owner articulation component -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- If a shore is closed after deleting `owner`, all ambient neighbors stay
inside `O`, and precisely the exceptional vertices are adjacent to `owner`,
then its oriented defect boundary is exactly the number of exceptional
vertices it contains. -/
theorem sum_boundary_eq_card_exceptional_of_erase_owner_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (O E S : Finset V) (owner : V)
    (hownerS : owner ∉ S)
    (hSsub : S ⊆ O)
    (hneighborsO : ∀ u ∈ O, D.neighborFinset u ⊆ O)
    (hclosed : ∀ u ∈ S,
      D.neighborFinset u ∩ (O.erase owner) ⊆ S)
    (hownerAdj : ∀ u ∈ O, D.Adj u owner ↔ u ∈ E) :
    ∑ u ∈ S, (D.neighborFinset u ∩ (Finset.univ \ S)).card =
      (E ∩ S).card := by
  classical
  have hrow (u : V) (huS : u ∈ S) :
      (D.neighborFinset u ∩ (Finset.univ \ S)).card =
        if u ∈ E then 1 else 0 := by
    have huO : u ∈ O := hSsub huS
    by_cases huE : u ∈ E
    · rw [if_pos huE]
      have huoAdj : D.Adj u owner := (hownerAdj u huO).mpr huE
      have hset : D.neighborFinset u ∩ (Finset.univ \ S) = {owner} := by
        ext v
        constructor
        · intro hv
          have hvParts := Finset.mem_inter.mp hv
          have hvN : v ∈ D.neighborFinset u := hvParts.1
          have hvO : v ∈ O := hneighborsO u huO hvN
          have hvNotS := (Finset.mem_sdiff.mp hvParts.2).2
          have hvOwner : v = owner := by
            by_contra hvne
            have hvErase : v ∈ O.erase owner :=
              Finset.mem_erase.mpr ⟨hvne, hvO⟩
            exact hvNotS (hclosed u huS (Finset.mem_inter.mpr ⟨hvN, hvErase⟩))
          simp [hvOwner]
        · intro hv
          have hvOwner : v = owner := Finset.mem_singleton.mp hv
          subst v
          exact Finset.mem_inter.mpr ⟨
            (D.mem_neighborFinset u owner).mpr huoAdj,
            Finset.mem_sdiff.mpr ⟨Finset.mem_univ owner, hownerS⟩⟩
      rw [hset]
      simp
    · rw [if_neg huE, Finset.card_eq_zero]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      have hvParts := Finset.mem_inter.mp hv
      have hvN : v ∈ D.neighborFinset u := hvParts.1
      have hvO : v ∈ O := hneighborsO u huO hvN
      have hvNotS := (Finset.mem_sdiff.mp hvParts.2).2
      by_cases hvOwner : v = owner
      · subst v
        exact huE ((hownerAdj u huO).mp
          ((D.mem_neighborFinset u owner).mp hvN))
      · have hvErase : v ∈ O.erase owner :=
          Finset.mem_erase.mpr ⟨hvOwner, hvO⟩
        exact hvNotS (hclosed u huS (Finset.mem_inter.mpr ⟨hvN, hvErase⟩))
  calc
    ∑ u ∈ S, (D.neighborFinset u ∩ (Finset.univ \ S)).card =
        ∑ u ∈ S, if u ∈ E then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      exact hrow u hu
    _ = (E ∩ S).card := by
      rw [Finset.sum_boole]
      apply congrArg Finset.card
      ext u
      simp [and_comm]

/-- Deleted-owner form of the `3 : 5` cross-edge double count.  It is enough
that the shore be closed inside `O.erase owner`, since both participating
colour classes avoid the owner. -/
theorem three_mul_regular_eq_five_mul_binOne_of_erase_owner_closed
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : SimpleGraph V) [DecidableRel D.Adj]
    (O S R B₁ : Finset V) (owner : V)
    (hRO : R ⊆ O.erase owner) (hB₁O : B₁ ⊆ O.erase owner)
    (hclosed : ∀ x ∈ S,
      D.neighborFinset x ∩ (O.erase owner) ⊆ S)
    (hR : ∀ x ∈ R, (D.neighborFinset x ∩ B₁).card = 3)
    (hB₁ : ∀ y ∈ B₁, (D.neighborFinset y ∩ R).card = 5) :
    3 * (R ∩ S).card = 5 * (B₁ ∩ S).card := by
  exact three_mul_card_inter_eq_five_mul_card_inter_of_relative_closed_shore
    D (O.erase owner) S R B₁ hRO hB₁O hclosed hR hB₁

/-- The exact `3r=5n₁` balance has the unique natural parametrization
`r=5k`, `n₁=3k`; adding `e` exceptional vertices gives shore order
`e+8k`. -/
theorem exists_articulation_scale_of_three_mul_regular_eq_five_mul_binOne
    (e r n₁ s : ℕ)
    (hbalance : 3 * r = 5 * n₁)
    (hcard : s = e + r + n₁) :
    ∃ k : ℕ, r = 5 * k ∧ n₁ = 3 * k ∧ s = e + 8 * k := by
  have hfive : 5 ∣ r := by omega
  obtain ⟨k, hk⟩ := hfive
  refine ⟨k, hk, ?_, ?_⟩
  · omega
  · omega

#print axioms sum_boundary_eq_card_exceptional_of_erase_owner_closed
#print axioms three_mul_regular_eq_five_mul_binOne_of_erase_owner_closed
#print axioms exists_articulation_scale_of_three_mul_regular_eq_five_mul_binOne

end

end Erdos85
