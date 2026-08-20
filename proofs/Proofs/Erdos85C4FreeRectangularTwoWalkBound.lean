import Proofs.Erdos85C4FreeSubsetCherryBound

/-! # Rectangular two-walk bounds in C4-free graphs -/

open Finset SimpleGraph

namespace Erdos85

/-- For disjoint target sets `S,T`, a C4-free graph has at most one center
for each ordered cross-pair. -/
theorem sum_neighbor_inter_card_mul_le_card_mul_card_of_not_containsC4
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) (S T : Finset V)
    (hST : Disjoint S T) :
    (∑ x : V, (G.neighborFinset x ∩ S).card *
      (G.neighborFinset x ∩ T).card) ≤ S.card * T.card := by
  classical
  let P : Finset (Σ _x : V, V × V) :=
    Finset.univ.sigma fun x ↦
      (G.neighborFinset x ∩ S).product (G.neighborFinset x ∩ T)
  let Q : Finset (V × V) := S.product T
  have hcardP : P.card =
      ∑ x : V, (G.neighborFinset x ∩ S).card *
        (G.neighborFinset x ∩ T).card := by
    dsimp only [P]
    rw [Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro x _
    simp
  have hcardQ : Q.card = S.card * T.card := by simp [Q]
  rw [← hcardP, ← hcardQ]
  apply Finset.card_le_card_of_injOn
    (fun p : (Σ _x : V, V × V) ↦ p.2)
  · intro p hp
    rcases p with ⟨x, ⟨s, t⟩⟩
    change ⟨x, (s, t)⟩ ∈ Finset.univ.sigma (fun x ↦
      (G.neighborFinset x ∩ S).product
        (G.neighborFinset x ∩ T)) at hp
    change (s, t) ∈ S.product T
    have hp' := (Finset.mem_sigma.mp hp).2
    rcases Finset.mem_product.mp hp' with ⟨hs, ht⟩
    exact Finset.mem_product.mpr
      ⟨(Finset.mem_inter.mp hs).2, (Finset.mem_inter.mp ht).2⟩
  · intro p hp q hq hpq
    rcases p with ⟨x, ⟨s, t⟩⟩
    rcases q with ⟨y, ⟨s', t'⟩⟩
    change (s, t) = (s', t') at hpq
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpq
    have hxy : x = y := by
      by_contra hne
      change ⟨x, (s, t)⟩ ∈ Finset.univ.sigma (fun x ↦
        (G.neighborFinset x ∩ S).product
          (G.neighborFinset x ∩ T)) at hp
      change ⟨y, (s, t)⟩ ∈ Finset.univ.sigma (fun x ↦
        (G.neighborFinset x ∩ S).product
          (G.neighborFinset x ∩ T)) at hq
      have hp' := Finset.mem_product.mp (Finset.mem_sigma.mp hp).2
      have hq' := Finset.mem_product.mp (Finset.mem_sigma.mp hq).2
      have hsS := (Finset.mem_inter.mp hp'.1).2
      have htT := (Finset.mem_inter.mp hp'.2).2
      have hst : s ≠ t := by
        intro h
        subst t
        exact Finset.disjoint_left.mp hST hsS htT
      have hsub : ({s, t} : Finset V) ⊆
          G.neighborFinset x ∩ G.neighborFinset y := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp hp'.1).1,
              (Finset.mem_inter.mp hq'.1).1⟩
        · exact Finset.mem_inter.mpr
            ⟨(Finset.mem_inter.mp hp'.2).1,
              (Finset.mem_inter.mp hq'.2).1⟩
      have hle := Finset.card_le_card hsub
      have hone := common_le_one_of_not_containsC4 hfree x y hne
      simp [hst] at hle
      omega
    subst y
    rfl

end Erdos85

#print axioms
  Erdos85.sum_neighbor_inter_card_mul_le_card_mul_card_of_not_containsC4
