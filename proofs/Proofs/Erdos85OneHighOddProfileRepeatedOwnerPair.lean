import Proofs.Erdos85OneHighOddProfileRepeatedOwner

/-!
# Decode the repeated exact owner selection

The executable odd-profile classifier returns three owner edges whose six
labels have cardinality below six.  Since every individual owner edge is
genuine, the repetition occurs between two different partition witnesses.
This module preserves the responsible witness pair and exact branch label.
-/

namespace Erdos85

private def ownerPairWitnessDecidable
    (refinement : List (List OneHighLabelPair)) (code : Fin 3)
    (i j : Fin 8) : Decidable
      (OneHighRefinementOwnerPairWitness refinement code i j) := by
  unfold OneHighRefinementOwnerPairWitness
  infer_instance

/-- Membership in the executable candidate list decodes back to the full
owner-pair witness. -/
theorem oneHighOwnerPairWitness_of_mem_candidates
    {refinement : List (List OneHighLabelPair)} {code : Fin 3}
    {i j : Fin 8}
    (hmem : (i, j) ∈ oneHighOwnerPairWitnessCandidates refinement code) :
    OneHighRefinementOwnerPairWitness refinement code i j := by
  have hdec := (List.mem_filter.mp hmem).2
  letI := ownerPairWitnessDecidable refinement code i j
  exact of_decide_eq_true hdec

/-- Three genuine two-element edges whose six listed endpoints have fewer
than six distinct values share an exact endpoint between two different
edges. -/
theorem three_pairEdges_card_lt_six_exists_pairwise_shared
    {L : Type*} [DecidableEq L]
    (a₀ b₀ a₁ b₁ a₂ b₂ : L)
    (h₀ : a₀ ≠ b₀) (h₁ : a₁ ≠ b₁) (h₂ : a₂ ≠ b₂)
    (hcard : [a₀, b₀, a₁, b₁, a₂, b₂].toFinset.card < 6) :
    ∃ z : L,
      (z ∈ ({a₀, b₀} : Finset L) ∧ z ∈ ({a₁, b₁} : Finset L)) ∨
      (z ∈ ({a₀, b₀} : Finset L) ∧ z ∈ ({a₂, b₂} : Finset L)) ∨
      (z ∈ ({a₁, b₁} : Finset L) ∧ z ∈ ({a₂, b₂} : Finset L)) := by
  by_contra hshared
  have hd₀₁ : Disjoint ({a₀, b₀} : Finset L) {a₁, b₁} := by
    rw [Finset.disjoint_left]
    intro z hz₀ hz₁
    exact hshared ⟨z, Or.inl ⟨hz₀, hz₁⟩⟩
  have hd₀₂ : Disjoint ({a₀, b₀} : Finset L) {a₂, b₂} := by
    rw [Finset.disjoint_left]
    intro z hz₀ hz₂
    exact hshared ⟨z, Or.inr (Or.inl ⟨hz₀, hz₂⟩)⟩
  have hd₁₂ : Disjoint ({a₁, b₁} : Finset L) {a₂, b₂} := by
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    exact hshared ⟨z, Or.inr (Or.inr ⟨hz₁, hz₂⟩)⟩
  have hdUnion : Disjoint
      (({a₀, b₀} : Finset L) ∪ {a₁, b₁}) {a₂, b₂} :=
    Finset.disjoint_union_left.mpr ⟨hd₀₂, hd₁₂⟩
  have hlist : [a₀, b₀, a₁, b₁, a₂, b₂].toFinset =
      (({a₀, b₀} : Finset L) ∪ {a₁, b₁}) ∪ {a₂, b₂} := by
    ext z
    simp only [List.mem_toFinset, List.mem_cons, List.not_mem_nil,
      or_false, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    aesop
  rw [hlist, Finset.card_union_of_disjoint hdUnion,
    Finset.card_union_of_disjoint hd₀₁] at hcard
  have hc₀ : ({a₀, b₀} : Finset L).card = 2 := by simp [h₀]
  have hc₁ : ({a₁, b₁} : Finset L).card = 2 := by simp [h₁]
  have hc₂ : ({a₂, b₂} : Finset L).card = 2 := by simp [h₂]
  omega

/-- Decode an executable repeated-owner selection to three full partition
witnesses and identify the exact owner label shared by a specific pair. -/
theorem oneHigh_repeatedOwnerSelection_exists_pairwise_shared
    (refinement : List (List OneHighLabelPair))
    (hsel : oneHighRefinementHasRepeatedOwnerSelection refinement = true) :
    ∃ e₀ e₁ e₂ : Fin 8 × Fin 8,
      OneHighRefinementOwnerPairWitness refinement 0 e₀.1 e₀.2 ∧
      OneHighRefinementOwnerPairWitness refinement 1 e₁.1 e₁.2 ∧
      OneHighRefinementOwnerPairWitness refinement 2 e₂.1 e₂.2 ∧
      ∃ z : Fin 8,
        (z ∈ ({e₀.1, e₀.2} : Finset (Fin 8)) ∧
          z ∈ ({e₁.1, e₁.2} : Finset (Fin 8))) ∨
        (z ∈ ({e₀.1, e₀.2} : Finset (Fin 8)) ∧
          z ∈ ({e₂.1, e₂.2} : Finset (Fin 8))) ∨
        (z ∈ ({e₁.1, e₁.2} : Finset (Fin 8)) ∧
          z ∈ ({e₂.1, e₂.2} : Finset (Fin 8))) := by
  obtain ⟨e₀, he₀, e₁, he₁, e₂, he₂, hcard⟩ :=
    oneHighRefinementHasRepeatedOwnerSelection_eq_true_iff refinement |>.mp hsel
  have hw₀ := oneHighOwnerPairWitness_of_mem_candidates he₀
  have hw₁ := oneHighOwnerPairWitness_of_mem_candidates he₁
  have hw₂ := oneHighOwnerPairWitness_of_mem_candidates he₂
  refine ⟨e₀, e₁, e₂, hw₀, hw₁, hw₂, ?_⟩
  exact three_pairEdges_card_lt_six_exists_pairwise_shared
    e₀.1 e₀.2 e₁.1 e₁.2 e₂.1 e₂.2
    hw₀.1 hw₁.1 hw₂.1 hcard

end Erdos85

#print axioms Erdos85.oneHighOwnerPairWitness_of_mem_candidates
#print axioms Erdos85.three_pairEdges_card_lt_six_exists_pairwise_shared
#print axioms Erdos85.oneHigh_repeatedOwnerSelection_exists_pairwise_shared
