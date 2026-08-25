import Proofs.Erdos85OneHighOddProfileCoherentLocalEdges

/-!
# A root repeated across two coherent odd-profile witnesses

The star-or-triangle split does not force one exact branch label to occur in
all three partition witnesses: the two labels in a root mate-pair may
alternate.  It does, however, force one of the four root mate-pairs to occur
in two of the witnesses.  This is the precise pigeonhole input needed by the
next mate-coupled escape count.
-/

namespace Erdos85

/-- Three genuine two-element edges with three-point union have a shared
endpoint between some pair of edges. -/
theorem finFour_three_edges_card_three_exists_pairwise_shared
    (a₀ b₀ a₁ b₁ a₂ b₂ : Fin 4)
    (h₀ : a₀ ≠ b₀) (h₁ : a₁ ≠ b₁) (h₂ : a₂ ≠ b₂)
    (hcard : ((finFourEdge a₀ b₀ ∪ finFourEdge a₁ b₁) ∪
      finFourEdge a₂ b₂).card = 3) :
    ∃ z : Fin 4,
      (z ∈ finFourEdge a₀ b₀ ∧ z ∈ finFourEdge a₁ b₁) ∨
      (z ∈ finFourEdge a₀ b₀ ∧ z ∈ finFourEdge a₂ b₂) ∨
      (z ∈ finFourEdge a₁ b₁ ∧ z ∈ finFourEdge a₂ b₂) := by
  by_contra hshared
  have hd₀₁ : Disjoint (finFourEdge a₀ b₀) (finFourEdge a₁ b₁) := by
    rw [Finset.disjoint_left]
    intro z hz₀ hz₁
    exact hshared ⟨z, Or.inl ⟨hz₀, hz₁⟩⟩
  have hd₀₂ : Disjoint (finFourEdge a₀ b₀) (finFourEdge a₂ b₂) := by
    rw [Finset.disjoint_left]
    intro z hz₀ hz₂
    exact hshared ⟨z, Or.inr (Or.inl ⟨hz₀, hz₂⟩)⟩
  have hd₁₂ : Disjoint (finFourEdge a₁ b₁) (finFourEdge a₂ b₂) := by
    rw [Finset.disjoint_left]
    intro z hz₁ hz₂
    exact hshared ⟨z, Or.inr (Or.inr ⟨hz₁, hz₂⟩)⟩
  have hdUnion : Disjoint
      (finFourEdge a₀ b₀ ∪ finFourEdge a₁ b₁)
      (finFourEdge a₂ b₂) :=
    Finset.disjoint_union_left.mpr ⟨hd₀₂, hd₁₂⟩
  rw [Finset.card_union_of_disjoint hdUnion,
    Finset.card_union_of_disjoint hd₀₁] at hcard
  have hc₀ : (finFourEdge a₀ b₀).card = 2 := by
    simp [finFourEdge, h₀]
  have hc₁ : (finFourEdge a₁ b₁).card = 2 := by
    simp [finFourEdge, h₁]
  have hc₂ : (finFourEdge a₂ b₂).card = 2 := by
    simp [finFourEdge, h₂]
  omega

/-- The coherent three-partition package always repeats a root mate-pair
across two witnesses, in both the star and triangle alternatives. -/
theorem oneHigh_coherentPartitionLocalEdges_exists_pairwise_sharedRoot
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q₀ : OneHighPartitionLocalEdgeWitness G hfree hv p 0)
    (q₁ : OneHighPartitionLocalEdgeWitness G hfree hv p 1)
    (q₂ : OneHighPartitionLocalEdgeWitness G hfree hv p 2)
    (hgeometry :
      (∃ z : Fin 4,
          z ∈ finFourEdge (oneHighRootPair (p.branchLabel q₀.s))
            (oneHighRootPair (p.branchLabel q₀.t)) ∧
          z ∈ finFourEdge (oneHighRootPair (p.branchLabel q₁.s))
            (oneHighRootPair (p.branchLabel q₁.t)) ∧
          z ∈ finFourEdge (oneHighRootPair (p.branchLabel q₂.s))
            (oneHighRootPair (p.branchLabel q₂.t))) ∨
        ((finFourEdge (oneHighRootPair (p.branchLabel q₀.s))
            (oneHighRootPair (p.branchLabel q₀.t)) ∪
          finFourEdge (oneHighRootPair (p.branchLabel q₁.s))
            (oneHighRootPair (p.branchLabel q₁.t))) ∪
          finFourEdge (oneHighRootPair (p.branchLabel q₂.s))
            (oneHighRootPair (p.branchLabel q₂.t))).card = 3) :
    ∃ z : Fin 4,
      (z ∈ finFourEdge (oneHighRootPair (p.branchLabel q₀.s))
          (oneHighRootPair (p.branchLabel q₀.t)) ∧
        z ∈ finFourEdge (oneHighRootPair (p.branchLabel q₁.s))
          (oneHighRootPair (p.branchLabel q₁.t))) ∨
      (z ∈ finFourEdge (oneHighRootPair (p.branchLabel q₀.s))
          (oneHighRootPair (p.branchLabel q₀.t)) ∧
        z ∈ finFourEdge (oneHighRootPair (p.branchLabel q₂.s))
          (oneHighRootPair (p.branchLabel q₂.t))) ∨
      (z ∈ finFourEdge (oneHighRootPair (p.branchLabel q₁.s))
          (oneHighRootPair (p.branchLabel q₁.t)) ∧
        z ∈ finFourEdge (oneHighRootPair (p.branchLabel q₂.s))
          (oneHighRootPair (p.branchLabel q₂.t))) := by
  rcases hgeometry with ⟨z, hz₀, hz₁, hz₂⟩ | htriangle
  · exact ⟨z, Or.inl ⟨hz₀, hz₁⟩⟩
  · have hrootNe {code : Fin 3}
        (q : OneHighPartitionLocalEdgeWitness G hfree hv p code) :
        oneHighRootPair (p.branchLabel q.s) ≠
          oneHighRootPair (p.branchLabel q.t) := by
      apply oneHighRootPair_ne_of_ne_of_ne_standardMate
      · exact fun h => q.source_ne (p.branchLabel.injective h)
      · intro hmate
        apply q.target_ne_mate
        apply p.branchLabel.injective
        rw [p.branch_mate]
        rw [hmate]
        exact (oneHighStandardMate_involutive _).symm
    have hrootNe₀ : oneHighRootPair (p.branchLabel q₀.s) ≠
        oneHighRootPair (p.branchLabel q₀.t) := by
      exact hrootNe q₀
    have hrootNe₁ : oneHighRootPair (p.branchLabel q₁.s) ≠
        oneHighRootPair (p.branchLabel q₁.t) := by
      exact hrootNe q₁
    have hrootNe₂ : oneHighRootPair (p.branchLabel q₂.s) ≠
        oneHighRootPair (p.branchLabel q₂.t) := by
      exact hrootNe q₂
    exact finFour_three_edges_card_three_exists_pairwise_shared
      _ _ _ _ _ _ hrootNe₀ hrootNe₁ hrootNe₂ htriangle

end Erdos85

#print axioms Erdos85.finFour_three_edges_card_three_exists_pairwise_shared
#print axioms Erdos85.oneHigh_coherentPartitionLocalEdges_exists_pairwise_sharedRoot
