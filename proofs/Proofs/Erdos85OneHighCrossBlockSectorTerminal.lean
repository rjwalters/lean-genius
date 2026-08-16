import Proofs.Erdos85MatchingMultiplicityRelabel
import Proofs.Erdos85OneHighStructuralTerminalInterface
import Proofs.Erdos85OneHighOddLabelTurn
import Proofs.Erdos85OneHighRootPairGraphDecoder

/-! # Concrete graph witnesses from the cross-block sector -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The graph-side realization of a full odd cross block.  Its four support
edges are represented by four actual nonconstant internal matching edges. -/
structure OneHighCrossBlockSourceConfiguration
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) where
  a₀ : {z : V // z ∈ G.neighborSet v}
  a₁ : {z : V // z ∈ G.neighborSet v}
  b₀ : {z : V // z ∈ G.neighborSet v}
  b₁ : {z : V // z ∈ G.neighborSet v}
  a_mate : p.mate a₀ = a₁
  b_mate : p.mate b₀ = b₁
  pair_ne : oneHighRootPair (p.branchLabel a₀) ≠
    oneHighRootPair (p.branchLabel b₀)
  q₀₀ : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj a₀ b₀
  q₀₁ : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj a₀ b₁
  q₁₀ : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj a₁ b₀
  q₁₁ : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj a₁ b₁

/-- A source for the primary cross-block edge is colored by neither mate
pair occurring in the block.  The other three fields carry the analogous
far-membership facts directly. -/
theorem OneHighCrossBlockSourceConfiguration.primarySourcePair_avoids_block
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (C : OneHighCrossBlockSourceConfiguration G hfree hv p) :
    ∀ q : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
        p.outer_degree p.mate p.mate_adj C.a₀ C.b₀,
      oneHighRootPair (p.branchLabel q.sourceEdge.1) ≠
          oneHighRootPair (p.branchLabel C.a₀) ∧
        oneHighRootPair (p.branchLabel q.sourceEdge.1) ≠
          oneHighRootPair (p.branchLabel C.b₀) := by
  intro q
  exact ⟨oneHighRootPair_ne_of_branch_mem_far p.mate p.branchLabel
      p.branch_mate q.sourceEdge.1 C.a₀ q.left_far,
    oneHighRootPair_ne_of_branch_mem_far p.mate p.branchLabel
      p.branch_mate q.sourceEdge.1 C.b₀ q.right_far⟩

private theorem four_finFour_values_avoiding_two_have_collision
    (i j s₀₀ s₀₁ s₁₀ s₁₁ : Fin 4) (hij : i ≠ j)
    (h₀₀ : s₀₀ ≠ i ∧ s₀₀ ≠ j)
    (h₀₁ : s₀₁ ≠ i ∧ s₀₁ ≠ j)
    (h₁₀ : s₁₀ ≠ i ∧ s₁₀ ≠ j)
    (h₁₁ : s₁₁ ≠ i ∧ s₁₁ ≠ j) :
    s₀₀ = s₀₁ ∨ s₀₀ = s₁₀ ∨ s₀₀ = s₁₁ ∨
      s₀₁ = s₁₀ ∨ s₀₁ = s₁₁ ∨ s₁₀ = s₁₁ := by
  decide +revert

private theorem oneHighRootPair_standardMate (x : Fin 8) :
    oneHighRootPair (oneHighStandardMate x) = oneHighRootPair x := by
  fin_cases x <;> decide

/-- Since the block occupies two of the four root-mate pairs, its four
concrete source edges use only the other two.  Thus two source edges
necessarily have the same root-pair color. -/
theorem OneHighCrossBlockSourceConfiguration.sourcePair_collision
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (C : OneHighCrossBlockSourceConfiguration G hfree hv p) :
    let color (q : OneHighAllMatchedVertices G v) :=
      oneHighRootPair (p.branchLabel q.1)
    color C.q₀₀.sourceEdge = color C.q₀₁.sourceEdge ∨
      color C.q₀₀.sourceEdge = color C.q₁₀.sourceEdge ∨
      color C.q₀₀.sourceEdge = color C.q₁₁.sourceEdge ∨
      color C.q₀₁.sourceEdge = color C.q₁₀.sourceEdge ∨
      color C.q₀₁.sourceEdge = color C.q₁₁.sourceEdge ∨
      color C.q₁₀.sourceEdge = color C.q₁₁.sourceEdge := by
  dsimp only
  have haPair : oneHighRootPair (p.branchLabel C.a₁) =
      oneHighRootPair (p.branchLabel C.a₀) := by
    rw [← C.a_mate, p.branch_mate]
    exact oneHighRootPair_standardMate _
  have hbPair : oneHighRootPair (p.branchLabel C.b₁) =
      oneHighRootPair (p.branchLabel C.b₀) := by
    rw [← C.b_mate, p.branch_mate]
    exact oneHighRootPair_standardMate _
  have avoids {a b : {z : V // z ∈ G.neighborSet v}}
      (q : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
        p.outer_degree p.mate p.mate_adj a b) :
      oneHighRootPair (p.branchLabel q.sourceEdge.1) ≠
          oneHighRootPair (p.branchLabel a) ∧
        oneHighRootPair (p.branchLabel q.sourceEdge.1) ≠
          oneHighRootPair (p.branchLabel b) :=
    ⟨oneHighRootPair_ne_of_branch_mem_far p.mate p.branchLabel
        p.branch_mate q.sourceEdge.1 a q.left_far,
      oneHighRootPair_ne_of_branch_mem_far p.mate p.branchLabel
        p.branch_mate q.sourceEdge.1 b q.right_far⟩
  apply four_finFour_values_avoiding_two_have_collision
    (oneHighRootPair (p.branchLabel C.a₀))
    (oneHighRootPair (p.branchLabel C.b₀))
  · exact C.pair_ne
  · exact avoids C.q₀₀
  · exact ⟨(avoids C.q₀₁).1, hbPair ▸ (avoids C.q₀₁).2⟩
  · exact ⟨haPair ▸ (avoids C.q₁₀).1, (avoids C.q₁₀).2⟩
  · exact ⟨haPair ▸ (avoids C.q₁₁).1,
      hbPair ▸ (avoids C.q₁₁).2⟩

/-- Graph-level form of the collision: two of the four concrete internal
edges are sourced either in the same branch or in the two branches of one
root-mate pair. -/
theorem OneHighCrossBlockSourceConfiguration.sourceBranch_collision
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (C : OneHighCrossBlockSourceConfiguration G hfree hv p) :
    let related (q r : OneHighAllMatchedVertices G v) :=
      q.1 = r.1 ∨ q.1 = p.mate r.1
    related C.q₀₀.sourceEdge C.q₀₁.sourceEdge ∨
      related C.q₀₀.sourceEdge C.q₁₀.sourceEdge ∨
      related C.q₀₀.sourceEdge C.q₁₁.sourceEdge ∨
      related C.q₀₁.sourceEdge C.q₁₀.sourceEdge ∨
      related C.q₀₁.sourceEdge C.q₁₁.sourceEdge ∨
      related C.q₁₀.sourceEdge C.q₁₁.sourceEdge := by
  dsimp only
  have decode {q r : OneHighAllMatchedVertices G v}
      (hqr : oneHighRootPair (p.branchLabel q.1) =
        oneHighRootPair (p.branchLabel r.1)) :
      q.1 = r.1 ∨ q.1 = p.mate r.1 :=
    (oneHighRootPair_branchLabel_eq_iff_eq_or_rootMate
      p.mate p.branchLabel p.branch_mate q.1 r.1).mp hqr
  rcases C.sourcePair_collision G hfree hv p with
    h | h | h | h | h | h
  · exact Or.inl (decode h)
  · exact Or.inr (Or.inl (decode h))
  · exact Or.inr (Or.inr (Or.inl (decode h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (decode h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (decode h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (decode h)))))

/-- Pull an odd support edge through the presentation's branch relabeling. -/
private theorem oddSupportAdj_unlabel
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    {a b : {z : V // z ∈ G.neighborSet v}}
    (h : (oddExchangedKeyLabelGraph
      (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)))).Adj (p.branchLabel a) (p.branchLabel b)) :
    (oddExchangedKeyLabelGraph
      (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
          p.mate p.mate_adj))).Adj a b := by
  refine ⟨fun hab => h.1 (congrArg p.branchLabel hab), ?_⟩
  rw [← exchangedMissPairMultiplicity_equiv
    (oneHighGlobalInternalMate G hfree v)
    (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
      p.mate p.mate_adj) p.branchLabel a b]
  simpa [Function.comp_def] using h.2

/-- A relabeled full cross block produces a concrete source configuration.
The two sides pull back to genuine root-mate pairs. -/
theorem OneHighOddSupportCrossBlockProp.exists_sourceConfiguration
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (hcross : OneHighOddSupportCrossBlockProp
      (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)))) :
    Nonempty (OneHighCrossBlockSourceConfiguration G hfree hv p) := by
  obtain ⟨i, j, hij, h₀₀, h₀₁, h₁₀, h₁₁⟩ := hcross
  let a₀ := p.branchLabel.symm (oneHighStandardPairLow i)
  let a₁ := p.branchLabel.symm (oneHighStandardPairHigh i)
  let b₀ := p.branchLabel.symm (oneHighStandardPairLow j)
  let b₁ := p.branchLabel.symm (oneHighStandardPairHigh j)
  have ha₀ : p.branchLabel a₀ = oneHighStandardPairLow i := by simp [a₀]
  have ha₁ : p.branchLabel a₁ = oneHighStandardPairHigh i := by simp [a₁]
  have hb₀ : p.branchLabel b₀ = oneHighStandardPairLow j := by simp [b₀]
  have hb₁ : p.branchLabel b₁ = oneHighStandardPairHigh j := by simp [b₁]
  have haMate : p.mate a₀ = a₁ := by
    apply p.branchLabel.injective
    rw [p.branch_mate, ha₀, ha₁]
    fin_cases i <;> decide
  have hbMate : p.mate b₀ = b₁ := by
    apply p.branchLabel.injective
    rw [p.branch_mate, hb₀, hb₁]
    fin_cases j <;> decide
  have hpair : oneHighRootPair (p.branchLabel a₀) ≠
      oneHighRootPair (p.branchLabel b₀) := by
    simp [ha₀, hb₀, oneHighRootPair, oneHighStandardPairLow]
    omega
  have source {x y : {z : V // z ∈ G.neighborSet v}}
      (hxy : (oddExchangedKeyLabelGraph
        (exchangedMissPairMultiplicity
          (oneHighGlobalInternalMate G hfree v)
          (fun z => p.branchLabel
            (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
              p.mate p.mate_adj z)))).Adj (p.branchLabel x) (p.branchLabel y)) :
      OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
        p.outer_degree p.mate p.mate_adj x y :=
    (exists_oneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
      p.outer_degree p.mate p.mate_adj
      (oddSupportAdj_unlabel G hfree hv p hxy)).some
  refine ⟨⟨a₀, a₁, b₀, b₁, haMate, hbMate, hpair, ?_, ?_, ?_, ?_⟩⟩
  · exact source (by simpa [ha₀, hb₀] using h₀₀)
  · exact source (by simpa [ha₀, hb₁] using h₀₁)
  · exact source (by simpa [ha₁, hb₀] using h₁₀)
  · exact source (by simpa [ha₁, hb₁] using h₁₁)

/-- The residual graph-side obligation obtained after replacing all four
abstract odd-support edges by actual internal matching-edge sources. -/
def OneHighConcreteCrossBlockSectorExcluded : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (hfree : ¬ containsC4 (Fin 49) G) →
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x) →
    (hHigh : (orderFortyNineHighVertices G).card = 1) →
    ∀ {v : Fin 49} (hv : G.degree v = 8)
      (p : OneHighRawV2Presentation G hfree v),
      Nonempty (OneHighCrossBlockSourceConfiguration G hfree hv p) → False

/-- Excluding the concrete four-source configuration closes the original
cross-block terminal sector. -/
theorem oneHighCrossBlockSectorExcluded_of_concrete
    (h : OneHighConcreteCrossBlockSectorExcluded) :
    OneHighCrossBlockSectorExcluded := by
  intro G _ _ _ hfree hmin hHigh v hv p
  dsimp only
  intro hcross
  exact h G inferInstance inferInstance inferInstance hfree hmin hHigh hv p
    (OneHighOddSupportCrossBlockProp.exists_sourceConfiguration
      G hfree hv p hcross)

end

end Erdos85
