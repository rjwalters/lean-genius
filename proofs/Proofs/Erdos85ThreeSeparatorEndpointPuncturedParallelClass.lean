import Proofs.Erdos85ThreeSeparatorEndpointParallelClass

/-! # The endpoint punctured parallel class -/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- B14 in generic form: the outside parts of pairwise-disjoint regular
neighborhoods exactly tile the complement of `U` and one exceptional point. -/
theorem endpoint_outside_neighbors_partition_punctured_complement
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X W U : Finset V) (c : V) (q : ℕ) (hq : 3 ≤ q)
    (hUdef : U = W.biUnion fun w => G.neighborFinset w)
    (hVcard : Fintype.card V = q * q)
    (hreg : ∀ x ∈ X, G.degree x = q)
    (hXcard : X.card = q - 2) (hUcard : U.card = 3 * q - 3)
    (hone : ∀ x ∈ X, (G.neighborFinset x ∩ U).card = 1)
    (hpair : ∀ x ∈ X, ∀ y ∈ X, x ≠ y →
      Disjoint (G.neighborFinset x) (G.neighborFinset y))
    (hcU : c ∉ U) (hcAnti : ∀ x ∈ X, ¬ G.Adj x c) :
    (∀ x ∈ X, (G.neighborFinset x \ U).card = q - 1) ∧
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y →
        Disjoint (G.neighborFinset x \ U) (G.neighborFinset y \ U)) ∧
      X.biUnion (fun x => G.neighborFinset x \ U) = univ \ (U ∪ {c}) := by
  let F : V → Finset V := fun x => G.neighborFinset x \ U
  have hFcard : ∀ x ∈ X, (F x).card = q - 1 := by
    intro x hx
    change (F x).card = q - 1
    rw [Finset.card_sdiff, G.card_neighborFinset_eq_degree, hreg x hx]
    have hinter : (U ∩ G.neighborFinset x).card = 1 := by
      rw [Finset.inter_comm]
      exact hone x hx
    rw [hinter]
  have hFpair : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → Disjoint (F x) (F y) := by
    intro x hx y hy hxy
    exact (hpair x hx y hy hxy).mono Finset.sdiff_subset Finset.sdiff_subset
  have hTargetCard : (univ \ (U ∪ {c}) : Finset V).card =
      (q - 2) * (q - 1) := by
    have hUc : (U ∪ {c}).card = U.card + 1 := by
      rw [Finset.card_union_of_disjoint]
      · simp
      · simp [Finset.disjoint_left, hcU]
    rw [Finset.card_sdiff]
    rw [Finset.inter_univ, Finset.card_univ, hVcard, hUc, hUcard]
    let a := q - 2
    have hqa : q = a + 2 := by dsimp [a]; omega
    have hqm1 : q - 1 = a + 1 := by dsimp [a]; omega
    have hthree : 3 * q - 3 = 3 * a + 3 := by omega
    have hle : 3 * q - 3 + 1 ≤ q * q := by
      rw [hthree, hqa]
      nlinarith
    apply (Nat.sub_eq_iff_eq_add' hle).2
    have hqm2 : q - 2 = a := rfl
    rw [hthree, hqm1, hqm2, hqa]
    ring
  refine ⟨by simpa [F] using hFcard, by simpa [F] using hFpair, ?_⟩
  have hcover := outside_pole_neighborhoods_eq_punctured_complement
    G X W c q
  dsimp only at hcover
  rw [← hUdef] at hcover
  apply hcover
  · exact hFpair
  · exact hFcard
  · exact hcAnti
  · rw [hTargetCard, hXcard]

#print axioms endpoint_outside_neighbors_partition_punctured_complement

end

end Erdos85
