import Proofs.Erdos85OrderFortyNineThreeHighTripleEmptyCandidates
import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeHighCrossMargins

namespace Erdos85

set_option maxRecDepth 100000 in
theorem threeBlockMask_degree_total (m : ThreeBlockMask) :
    (∑ i : Fin 5, encodedRowDegree (oneHighBranchBitAdj m.val i)) = 4 := by
  obtain ⟨k,rfl⟩ := finFiveMatchingMaskCode_surjective m
  have h : ∀ k : Fin 15,
      (∑ i : Fin 5, encodedRowDegree (oneHighBranchBitAdj (finFiveMatchingMaskCode k).val i)) = 4 := by
    decide
  exact h k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem threeBlockMatchingAdj_degree_total
    (m : Fin 3 → ThreeBlockMask) (π : Equiv.Perm (Fin 5)) :
    (∑ p : Fin 3 × Fin 5, encodedRowDegree (threeBlockMatchingAdj (fun k => (m k).val) π p)) = 42 := by
  have h0 := threeBlockMask_degree_total (m 0)
  have h1 := threeBlockMask_degree_total (m 1)
  have h2 := threeBlockMask_degree_total (m 2)
  have hp : ∀ x : Fin 5, (Finset.univ.filter fun y => π y = x).card = 1 := by
    intro x
    have he : (Finset.univ.filter fun y => π y = x) = {π.symm x} := by
      ext y
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
      constructor
      · intro h
        apply π.injective
        simpa using h
      · intro h
        rw [h]
        exact π.apply_symm_apply x
    rw [he]
    simp
  simp only [encodedRowDegree] at h0 h1 h2
  simp only [encodedRowDegree,Finset.card_eq_sum_ones,Finset.sum_filter]
  simp only [Fintype.sum_prod_type,Fin.sum_univ_three]
  simp [threeBlockMatchingAdj,Finset.sum_add_distrib,hp]
  omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem threeBlockDeficientMatchingAdj_degree_total
    (m : Fin 3 → ThreeBlockMask) (π : Equiv.Perm (Fin 5)) (d : Fin 5) :
    (∑ p : Fin 3 × Fin 5, encodedRowDegree
      (threeBlockDeficientMatchingAdj (fun k => (m k).val) π d p)) = 40 := by
  have h0 := threeBlockMask_degree_total (m 0)
  have h1 := threeBlockMask_degree_total (m 1)
  have h2 := threeBlockMask_degree_total (m 2)
  have hp : (∑ x : Fin 5, (Finset.univ.filter fun y => x ≠ d ∧ π x = y).card) = 4 ∧
      (∑ x : Fin 5, (Finset.univ.filter fun y => y ≠ d ∧ π y = x).card) = 4 := by
    obtain ⟨k,rfl⟩ := finFivePermutationCode_surjective π
    have h : ∀ k : Fin 120, ∀ d : Fin 5,
        (∑ x : Fin 5, (Finset.univ.filter fun y => x ≠ d ∧ finFivePermutationCode k x = y).card) = 4 ∧
        (∑ x : Fin 5, (Finset.univ.filter fun y => y ≠ d ∧ finFivePermutationCode k y = x).card) = 4 := by
      decide
    exact h k d
  simp only [ne_eq] at hp
  simp only [encodedRowDegree] at h0 h1 h2
  simp only [encodedRowDegree,Finset.card_eq_sum_ones,Finset.sum_filter]
  simp only [Fintype.sum_prod_type,Fin.sum_univ_three]
  simp [threeBlockDeficientMatchingAdj,Finset.sum_add_distrib]
  omega

theorem encodedRowDegree_total_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (B : β → β → Bool) :
    (∑ x : α, encodedRowDegree (fun y => B (e x) (e y))) =
      ∑ x : β, encodedRowDegree (B x) := by
  classical
  simp only [encodedRowDegree,Finset.card_eq_sum_ones,Finset.sum_filter]
  apply Fintype.sum_equiv e
  intro x
  exact Fintype.sum_equiv e _ _ (fun y => rfl)

theorem threeHighFullUnionAdj_degree_total (p : ThreeBlockFullParameters) :
    (∑ i : Fin 15, encodedRowDegree (threeHighFullUnionAdj p i)) = 42 := by
  unfold threeHighFullUnionAdj
  rw [encodedRowDegree_total_equiv]
  exact threeBlockMatchingAdj_degree_total p.1 p.2

theorem threeHighDeficientUnionAdj_degree_total (p : ThreeBlockDeficientParameters) :
    (∑ i : Fin 15, encodedRowDegree (threeHighDeficientUnionAdj p i)) = 40 := by
  unfold threeHighDeficientUnionAdj
  rw [encodedRowDegree_total_equiv]
  exact threeBlockDeficientMatchingAdj_degree_total p.1.1 p.1.2 p.2

end Erdos85
#print axioms Erdos85.threeBlockMask_degree_total
#print axioms Erdos85.threeBlockMatchingAdj_degree_total

#print axioms Erdos85.threeBlockDeficientMatchingAdj_degree_total

#print axioms Erdos85.encodedRowDegree_total_equiv
#print axioms Erdos85.threeHighFullUnionAdj_degree_total
#print axioms Erdos85.threeHighDeficientUnionAdj_degree_total
