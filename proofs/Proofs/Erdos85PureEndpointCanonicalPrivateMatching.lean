import Proofs.Erdos85PureEndpointFourClassProfile
import Proofs.Erdos85PartialBaerEndpointPrivatePoints
import Proofs.Erdos85DyadicStoppingSupportDefectPenalizedCherrySqueeze

/-!
# Canonical private matching at the pure endpoint

The four-class endpoint profile is now connected to the graph-facing
partial-Baer matching theorem.  Saturation of the C4 cherry budget forces
the canonical exceptional family to contain no second-order-defect pair;
the same profile removes replication three.  Hence every exceptional line
has a private point, and these points form an injective matching.
-/

open Finset SimpleGraph

namespace Erdos85

noncomputable section

/-- At the pure endpoint, a canonical replication partition together with
the shore and incidence identities forces an injective private-neighbor
matching.  The hypotheses `hout` and `hrepUpper` are exactly the two graph
facts supplied by the full-line final-layer construction: exceptional lines
live wholly on the shore, and shore replication is at most three. -/
theorem pureEndpoint_fourClass_defectIndependent_and_privateMatching
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (C S : Finset V) (hCcard : C.card = q)
    (hline : ∀ i ∈ C, G.degree i = q)
    (hshore : 2 * S.card = q * q + q)
    (hout : ∀ p ∉ S, (G.neighborFinset p ∩ C).card = 0)
    (hrepUpper : ∀ p ∈ S, (G.neighborFinset p ∩ C).card ≤ 3) :
    (∀ i ∈ C, ∀ j ∈ C, i ≠ j →
      ¬(secondOrderDefectGraph G).Adj i j) ∧
    ∃ p : {i // i ∈ C} → V, Function.Injective p ∧
      ∀ i, G.Adj i.1 (p i) ∧ G.neighborFinset (p i) ∩ C = {i.1} := by
  classical
  let rep : V → ℕ := fun p => (G.neighborFinset p ∩ C).card
  let N₀ := S.filter fun p => rep p = 0
  let N₁ := S.filter fun p => rep p = 1
  let N₂ := S.filter fun p => rep p = 2
  let N₃ := S.filter fun p => rep p = 3
  have hcases : ∀ p ∈ S,
      rep p = 0 ∨ rep p = 1 ∨ rep p = 2 ∨ rep p = 3 := by
    intro p hp
    have hup : rep p ≤ 3 := by
      simpa [rep] using hrepUpper p hp
    interval_cases rep p <;> simp_all
  have hpairDisj : ∀ {i k : ℕ}, i ≠ k →
      Disjoint (S.filter fun p => rep p = i)
        (S.filter fun p => rep p = k) := by
    intro i k hik
    rw [Finset.disjoint_left]
    intro p hpi hpk
    exact hik ((Finset.mem_filter.mp hpi).2.symm.trans
      (Finset.mem_filter.mp hpk).2)
  have hd01 : Disjoint N₀ N₁ := hpairDisj (by omega)
  have hd012 : Disjoint (N₀ ∪ N₁) N₂ := by
    rw [Finset.disjoint_left]
    intro p hp hp₂
    rcases Finset.mem_union.mp hp with hp₀ | hp₁
    · exact Finset.disjoint_left.mp (hpairDisj (by omega)) hp₀ hp₂
    · exact Finset.disjoint_left.mp (hpairDisj (by omega)) hp₁ hp₂
  have hd0123 : Disjoint (N₀ ∪ N₁ ∪ N₂) N₃ := by
    rw [Finset.disjoint_left]
    intro p hp hp₃
    rcases Finset.mem_union.mp hp with hp01 | hp₂
    · rcases Finset.mem_union.mp hp01 with hp₀ | hp₁
      · exact Finset.disjoint_left.mp (hpairDisj (by omega)) hp₀ hp₃
      · exact Finset.disjoint_left.mp (hpairDisj (by omega)) hp₁ hp₃
    · exact Finset.disjoint_left.mp (hpairDisj (by omega)) hp₂ hp₃
  have hunion : N₀ ∪ N₁ ∪ N₂ ∪ N₃ = S := by
    apply Finset.Subset.antisymm
    · apply Finset.union_subset
      · apply Finset.union_subset
        · apply Finset.union_subset
          · intro p hp; exact (Finset.mem_filter.mp hp).1
          · intro p hp; exact (Finset.mem_filter.mp hp).1
        · intro p hp; exact (Finset.mem_filter.mp hp).1
      · intro p hp; exact (Finset.mem_filter.mp hp).1
    · intro p hp
      rcases hcases p hp with h₀ | h₁ | h₂ | h₃
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h₀⟩)))
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h₁⟩)))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.mpr ⟨hp, h₂⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, h₃⟩)
  have hclasses : N₀.card + N₁.card + N₂.card + N₃.card = S.card := by
    rw [← Finset.card_union_of_disjoint hd01,
      ← Finset.card_union_of_disjoint hd012,
      ← Finset.card_union_of_disjoint hd0123, hunion]
  have hsumRestrict : (∑ p ∈ S, rep p) = ∑ p : V, rep p := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro p _ hp
    exact hout p hp
  have hsumAll : (∑ p : V, rep p) = q * C.card := by
    have hinc := sum_card_neighbor_inter_eq_sum_degree G C
    change (∑ p : V, rep p) = _
    rw [hinc]
    calc
      (∑ a ∈ C, G.degree a) = ∑ _a ∈ C, q := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hline a ha
      _ = q * C.card := by simp [Nat.mul_comm]
  have hsumClasses : (∑ p ∈ S, rep p) =
      N₁.card + 2 * N₂.card + 3 * N₃.card := by
    rw [← hunion, Finset.sum_union hd0123,
      Finset.sum_union hd012, Finset.sum_union hd01]
    have hsum₀ : (∑ p ∈ N₀, rep p) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      exact (Finset.mem_filter.mp hp).2
    have hsum₁ : (∑ p ∈ N₁, rep p) = N₁.card := by
      calc
        (∑ p ∈ N₁, rep p) = ∑ _p ∈ N₁, 1 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact (Finset.mem_filter.mp hp).2
        _ = N₁.card := by simp
    have hsum₂ : (∑ p ∈ N₂, rep p) = 2 * N₂.card := by
      calc
        (∑ p ∈ N₂, rep p) = ∑ _p ∈ N₂, 2 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact (Finset.mem_filter.mp hp).2
        _ = 2 * N₂.card := by simp [Nat.mul_comm]
    have hsum₃ : (∑ p ∈ N₃, rep p) = 3 * N₃.card := by
      calc
        (∑ p ∈ N₃, rep p) = ∑ _p ∈ N₃, 3 := by
          apply Finset.sum_congr rfl
          intro p hp
          exact (Finset.mem_filter.mp hp).2
        _ = 3 * N₃.card := by simp [Nat.mul_comm]
    rw [hsum₀, hsum₁, hsum₂, hsum₃]
    omega
  have hincidence : N₁.card + 2 * N₂.card + 3 * N₃.card = q * q := by
    rw [← hsumClasses, hsumRestrict, hsumAll, hCcard]
  have hcherry :=
    sum_choose_card_neighbor_inter_le_choose_card_of_not_containsC4
      G hfree C
  have hcherryRestrict :
      (∑ p ∈ S, (rep p).choose 2) ≤ C.card.choose 2 := by
    calc
      (∑ p ∈ S, (rep p).choose 2) ≤
          ∑ p : V, (rep p).choose 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun _ _ _ => Nat.zero_le _)
      _ ≤ C.card.choose 2 := hcherry
  have hcherryClasses :
      (∑ p ∈ S, (rep p).choose 2) = N₂.card + 3 * N₃.card := by
    rw [← hunion, Finset.sum_union hd0123,
      Finset.sum_union hd012, Finset.sum_union hd01]
    have hsum₀ : (∑ p ∈ N₀, (rep p).choose 2) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
      decide
    have hsum₁ : (∑ p ∈ N₁, (rep p).choose 2) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
      decide
    have hsum₂ : (∑ p ∈ N₂, (rep p).choose 2) = N₂.card := by
      calc
        (∑ p ∈ N₂, (rep p).choose 2) = ∑ _p ∈ N₂, 1 := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
          decide
        _ = N₂.card := by simp
    have hsum₃ : (∑ p ∈ N₃, (rep p).choose 2) = 3 * N₃.card := by
      calc
        (∑ p ∈ N₃, (rep p).choose 2) = ∑ _p ∈ N₃, 3 := by
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
          decide
        _ = 3 * N₃.card := by simp [Nat.mul_comm]
    rw [hsum₀, hsum₁, hsum₂, hsum₃]
    omega
  have hpairs : 2 * N₂.card + 6 * N₃.card ≤ q * (q - 1) := by
    have hle : N₂.card + 3 * N₃.card ≤ C.card.choose 2 := by
      rw [← hcherryClasses]
      exact hcherryRestrict
    rw [hCcard] at hle
    nlinarith [two_mul_choose_two q]
  obtain ⟨_hn₀, _hn₁, hn₃, _hn₂, hpairsEq⟩ :=
    binarySquare_pureExceptional_fourClass_endpoint_profile
      hshore hclasses hincidence hpairs
  have hcherryEq : (∑ p : V, (rep p).choose 2) = C.card.choose 2 := by
    have houtChoose : ∀ p ∉ S, (rep p).choose 2 = 0 := by
      intro p hp
      rw [show rep p = 0 by simpa [rep] using hout p hp]
      decide
    have hrestrict : (∑ p ∈ S, (rep p).choose 2) =
        ∑ p : V, (rep p).choose 2 := by
      apply Finset.sum_subset (Finset.subset_univ S)
      intro p _ hp
      exact houtChoose p hp
    rw [← hrestrict, hcherryClasses, hCcard]
    rw [hn₃] at hpairsEq ⊢
    simp only [mul_zero, add_zero] at hpairsEq ⊢
    nlinarith [two_mul_choose_two q]
  have hdefectZero : (secondOrderDefectPairs G C).card = 0 := by
    have hpen := sum_choose_card_neighbor_inter_le_choose_card_sub_forbidden
      G hfree C (secondOrderDefectPairs G C)
      (secondOrderDefectPairs_subset_powersetCard G C)
      (secondOrderDefectPairs_forbidden_commonNeighbor G hfree C)
    change (∑ p : V, (rep p).choose 2) ≤
      C.card.choose 2 - (secondOrderDefectPairs G C).card at hpen
    have hdefectLe : (secondOrderDefectPairs G C).card ≤ C.card.choose 2 := by
      have := Finset.card_le_card (secondOrderDefectPairs_subset_powersetCard G C)
      simpa only [Finset.card_powersetCard] using this
    rw [hcherryEq] at hpen
    omega
  have hDindependent : ∀ i ∈ C, ∀ j ∈ C, i ≠ j →
      ¬(secondOrderDefectGraph G).Adj i j := by
    intro i hi j hj hij hDij
    have hp : ({i, j} : Finset V) ∈ secondOrderDefectPairs G C := by
      apply Finset.mem_filter.mpr
      constructor
      · apply Finset.mem_powersetCard.mpr
        constructor
        · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
          exact ⟨hi, hj⟩
        · exact Finset.card_pair hij
      · intro u hu v hv huv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
        rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
        · exact (huv rfl).elim
        · exact hDij
        · exact hDij.symm
        · exact (huv rfl).elim
    have : 0 < (secondOrderDefectPairs G C).card :=
      Finset.card_pos.mpr ⟨{i, j}, hp⟩
    omega
  have htripleZero :
      (∑ x : V, ((G.neighborFinset x ∩ C).card).choose 3) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    by_cases hxS : x ∈ S
    · have hxle : rep x ≤ 3 := by
        simpa [rep] using hrepUpper x hxS
      have hxne : rep x ≠ 3 := by
        intro hx3
        have hxN₃ : x ∈ N₃ := Finset.mem_filter.mpr ⟨hxS, hx3⟩
        have : 0 < N₃.card := Finset.card_pos.mpr ⟨x, hxN₃⟩
        omega
      have hx2 : rep x ≤ 2 := by omega
      rw [show (G.neighborFinset x ∩ C).card = rep x by rfl]
      interval_cases rep x <;> decide
    · rw [hout x hxS]
      decide
  exact ⟨hDindependent,
    exists_injective_privateNeighbor_of_noDefectEdges_noTripleMass
      G hfree C hCcard hline hDindependent htripleZero⟩

/-- Matching-only projection of the full pure-endpoint structure theorem. -/
theorem exists_injective_privateNeighbor_of_pureEndpoint_fourClass
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G) {q : ℕ}
    (C S : Finset V) (hCcard : C.card = q)
    (hline : ∀ i ∈ C, G.degree i = q)
    (hshore : 2 * S.card = q * q + q)
    (hout : ∀ p ∉ S, (G.neighborFinset p ∩ C).card = 0)
    (hrepUpper : ∀ p ∈ S, (G.neighborFinset p ∩ C).card ≤ 3) :
    ∃ p : {i // i ∈ C} → V, Function.Injective p ∧
      ∀ i, G.Adj i.1 (p i) ∧ G.neighborFinset (p i) ∩ C = {i.1} :=
  (pureEndpoint_fourClass_defectIndependent_and_privateMatching
    G hfree C S hCcard hline hshore hout hrepUpper).2

end

end Erdos85

#print axioms Erdos85.exists_injective_privateNeighbor_of_pureEndpoint_fourClass
#print axioms
  Erdos85.pureEndpoint_fourClass_defectIndependent_and_privateMatching
