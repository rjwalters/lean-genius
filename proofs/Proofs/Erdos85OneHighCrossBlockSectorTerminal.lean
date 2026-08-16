import Proofs.Erdos85MatchingMultiplicityRelabel
import Proofs.Erdos85OneHighStructuralTerminalInterface
import Proofs.Erdos85OneHighOddLabelTurn
import Proofs.Erdos85OneHighRootPairGraphDecoder
import Proofs.Erdos85OneHighRepeatedSourceCapacity
import Proofs.Erdos85OneHighTurnPairingBridge

/-! # Concrete graph witnesses from the cross-block sector -/

namespace Erdos85

open SimpleGraph

noncomputable section

private theorem minMax_pair_ne_of_left_not_endpoint
    {L : Type*} [LinearOrder L] {a b c d : L}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) :
    (min a b, max a b) ≠ (min c d, max c d) := by
  intro hpair
  rcases lt_or_gt_of_ne hab with hablt | hbalt <;>
    rcases lt_or_gt_of_ne hcd with hcdlt | hdclt
  · rw [min_eq_left hablt.le, max_eq_right hablt.le,
      min_eq_left hcdlt.le, max_eq_right hcdlt.le] at hpair
    exact hac (Prod.mk.inj hpair).1
  · rw [min_eq_left hablt.le, max_eq_right hablt.le,
      min_eq_right hdclt.le, max_eq_left hdclt.le] at hpair
    exact had (Prod.mk.inj hpair).1
  · rw [min_eq_right hbalt.le, max_eq_left hbalt.le,
      min_eq_left hcdlt.le, max_eq_right hcdlt.le] at hpair
    exact had (Prod.mk.inj hpair).2
  · rw [min_eq_right hbalt.le, max_eq_left hbalt.le,
      min_eq_right hdclt.le, max_eq_left hdclt.le] at hpair
    exact hac (Prod.mk.inj hpair).2

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

/-- Exact executable-row package produced by a saturated concrete cross
source: the witness's canonical miss pair occurs in a pairing row of length
two. -/
structure OneHighSaturatedCrossSourcePairingWitness
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) where
  a : {z : V // z ∈ G.neighborSet v}
  b : {z : V // z ∈ G.neighborSet v}
  q : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj a b
  saturated : oneHighFamilyInternalEdges p.profile
    (p.branchLabel q.sourceEdge.1) = 2
  pair_mem :
    oneHighCanonicalLabelPair (p.branchLabel a) (p.branchLabel b) ∈
      oneHighGraphSourcePairing G hfree hv p
        (p.branchLabel q.sourceEdge.1)
  row_length :
    (oneHighGraphSourcePairing G hfree hv p
      (p.branchLabel q.sourceEdge.1)).length = 2

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

/-- The four K₂,₂ support edges have four different unordered keys, so
their concrete oriented matching-edge witnesses are pairwise distinct. -/
theorem OneHighCrossBlockSourceConfiguration.sourceEdges_pairwise_ne
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (C : OneHighCrossBlockSourceConfiguration G hfree hv p) :
    C.q₀₀.sourceEdge ≠ C.q₀₁.sourceEdge ∧
      C.q₀₀.sourceEdge ≠ C.q₁₀.sourceEdge ∧
      C.q₀₀.sourceEdge ≠ C.q₁₁.sourceEdge ∧
      C.q₀₁.sourceEdge ≠ C.q₁₀.sourceEdge ∧
      C.q₀₁.sourceEdge ≠ C.q₁₁.sourceEdge ∧
      C.q₁₀.sourceEdge ≠ C.q₁₁.sourceEdge := by
  have ha₀a₁ : C.a₀ ≠ C.a₁ := by
    intro h
    have hadj := p.mate_adj C.a₀
    rw [C.a_mate, ← h] at hadj
    exact G.loopless.irrefl C.a₀.1 hadj
  have hb₀b₁ : C.b₀ ≠ C.b₁ := by
    intro h
    have hadj := p.mate_adj C.b₀
    rw [C.b_mate, ← h] at hadj
    exact G.loopless.irrefl C.b₀.1 hadj
  have haPair : oneHighRootPair (p.branchLabel C.a₁) =
      oneHighRootPair (p.branchLabel C.a₀) := by
    rw [← C.a_mate, p.branch_mate]
    exact oneHighRootPair_standardMate _
  have hbPair : oneHighRootPair (p.branchLabel C.b₁) =
      oneHighRootPair (p.branchLabel C.b₀) := by
    rw [← C.b_mate, p.branch_mate]
    exact oneHighRootPair_standardMate _
  have crossNe (a : {z : V // z ∈ G.neighborSet v})
      (ha : a = C.a₀ ∨ a = C.a₁)
      (b : {z : V // z ∈ G.neighborSet v})
      (hb : b = C.b₀ ∨ b = C.b₁) : a ≠ b := by
    intro hab
    apply C.pair_ne
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact congrArg (fun x => oneHighRootPair (p.branchLabel x)) hab
    · exact (congrArg (fun x => oneHighRootPair (p.branchLabel x)) hab).trans hbPair
    · exact haPair.symm.trans
        (congrArg (fun x => oneHighRootPair (p.branchLabel x)) hab)
    · exact haPair.symm.trans
        ((congrArg (fun x => oneHighRootPair (p.branchLabel x)) hab).trans hbPair)
  have keyNe {q r : OneHighAllMatchedVertices G v}
      {a b c d : {z : V // z ∈ G.neighborSet v}}
      (hq : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
        p.outer_degree p.mate p.mate_adj a b)
      (hr : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
        p.outer_degree p.mate p.mate_adj c d)
      (hkey : (min a b, max a b) ≠ (min c d, max c d))
      (eqQ : q = hq.sourceEdge) (eqR : r = hr.sourceEdge) : q ≠ r := by
    subst q
    subst r
    intro heq
    apply hkey
    rw [← hq.key_eq, ← hr.key_eq, heq]
  have h00_01 : (min C.a₀ C.b₀, max C.a₀ C.b₀) ≠
      (min C.a₀ C.b₁, max C.a₀ C.b₁) := by
    simpa [min_comm, max_comm] using minMax_pair_ne_of_left_not_endpoint
      (crossNe C.a₀ (Or.inl rfl) C.b₀ (Or.inl rfl)).symm
      (crossNe C.a₀ (Or.inl rfl) C.b₁ (Or.inr rfl))
      (crossNe C.a₀ (Or.inl rfl) C.b₀ (Or.inl rfl)).symm hb₀b₁
  have h00_10 := minMax_pair_ne_of_left_not_endpoint
    (crossNe C.a₀ (Or.inl rfl) C.b₀ (Or.inl rfl))
    (crossNe C.a₁ (Or.inr rfl) C.b₀ (Or.inl rfl)) ha₀a₁
    (crossNe C.a₀ (Or.inl rfl) C.b₀ (Or.inl rfl))
  have h00_11 := minMax_pair_ne_of_left_not_endpoint
    (crossNe C.a₀ (Or.inl rfl) C.b₀ (Or.inl rfl))
    (crossNe C.a₁ (Or.inr rfl) C.b₁ (Or.inr rfl)) ha₀a₁
    (crossNe C.a₀ (Or.inl rfl) C.b₁ (Or.inr rfl))
  have h01_10 := minMax_pair_ne_of_left_not_endpoint
    (crossNe C.a₀ (Or.inl rfl) C.b₁ (Or.inr rfl))
    (crossNe C.a₁ (Or.inr rfl) C.b₀ (Or.inl rfl)) ha₀a₁
    (crossNe C.a₀ (Or.inl rfl) C.b₀ (Or.inl rfl))
  have h01_11 := minMax_pair_ne_of_left_not_endpoint
    (crossNe C.a₀ (Or.inl rfl) C.b₁ (Or.inr rfl))
    (crossNe C.a₁ (Or.inr rfl) C.b₁ (Or.inr rfl)) ha₀a₁
    (crossNe C.a₀ (Or.inl rfl) C.b₁ (Or.inr rfl))
  have h10_11 : (min C.a₁ C.b₀, max C.a₁ C.b₀) ≠
      (min C.a₁ C.b₁, max C.a₁ C.b₁) := by
    simpa [min_comm, max_comm] using minMax_pair_ne_of_left_not_endpoint
      (crossNe C.a₁ (Or.inr rfl) C.b₀ (Or.inl rfl)).symm
      (crossNe C.a₁ (Or.inr rfl) C.b₁ (Or.inr rfl))
      (crossNe C.a₁ (Or.inr rfl) C.b₀ (Or.inl rfl)).symm hb₀b₁
  exact ⟨keyNe C.q₀₀ C.q₀₁ h00_01 rfl rfl,
    keyNe C.q₀₀ C.q₁₀ h00_10 rfl rfl,
    keyNe C.q₀₀ C.q₁₁ h00_11 rfl rfl,
    keyNe C.q₀₁ C.q₁₀ h01_10 rfl rfl,
    keyNe C.q₀₁ C.q₁₁ h01_11 rfl rfl,
    keyNe C.q₁₀ C.q₁₁ h10_11 rfl rfl⟩

/-- Combined nondegenerate collision interface: one explicitly listed pair
consists of distinct matching edges whose owner branches are equal or mates. -/
theorem OneHighCrossBlockSourceConfiguration.distinct_same_or_mate_collision
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (C : OneHighCrossBlockSourceConfiguration G hfree hv p) :
    (C.q₀₀.sourceEdge ≠ C.q₀₁.sourceEdge ∧
      (C.q₀₀.sourceEdge.1 = C.q₀₁.sourceEdge.1 ∨
       C.q₀₀.sourceEdge.1 = p.mate C.q₀₁.sourceEdge.1)) ∨
    (C.q₀₀.sourceEdge ≠ C.q₁₀.sourceEdge ∧
      (C.q₀₀.sourceEdge.1 = C.q₁₀.sourceEdge.1 ∨
       C.q₀₀.sourceEdge.1 = p.mate C.q₁₀.sourceEdge.1)) ∨
    (C.q₀₀.sourceEdge ≠ C.q₁₁.sourceEdge ∧
      (C.q₀₀.sourceEdge.1 = C.q₁₁.sourceEdge.1 ∨
       C.q₀₀.sourceEdge.1 = p.mate C.q₁₁.sourceEdge.1)) ∨
    (C.q₀₁.sourceEdge ≠ C.q₁₀.sourceEdge ∧
      (C.q₀₁.sourceEdge.1 = C.q₁₀.sourceEdge.1 ∨
       C.q₀₁.sourceEdge.1 = p.mate C.q₁₀.sourceEdge.1)) ∨
    (C.q₀₁.sourceEdge ≠ C.q₁₁.sourceEdge ∧
      (C.q₀₁.sourceEdge.1 = C.q₁₁.sourceEdge.1 ∨
       C.q₀₁.sourceEdge.1 = p.mate C.q₁₁.sourceEdge.1)) ∨
    (C.q₁₀.sourceEdge ≠ C.q₁₁.sourceEdge ∧
      (C.q₁₀.sourceEdge.1 = C.q₁₁.sourceEdge.1 ∨
       C.q₁₀.sourceEdge.1 = p.mate C.q₁₁.sourceEdge.1)) := by
  have hn := C.sourceEdges_pairwise_ne G hfree hv p
  rcases C.sourceBranch_collision G hfree hv p with h | h | h | h | h | h
  · exact Or.inl ⟨hn.1, h⟩
  · exact Or.inr (Or.inl ⟨hn.2.1, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hn.2.2.1, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hn.2.2.2.1, h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hn.2.2.2.2.1, h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr ⟨hn.2.2.2.2.2, h⟩))))

/-- The genuinely residual mate-owner alternatives after same-owner
collisions have been converted into saturated branch capacity. -/
def OneHighCrossBlockMateOwnerCollision
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (C : OneHighCrossBlockSourceConfiguration G hfree hv p) : Prop :=
  (C.q₀₀.sourceEdge ≠ C.q₀₁.sourceEdge ∧
    C.q₀₀.sourceEdge.1 = p.mate C.q₀₁.sourceEdge.1) ∨
  (C.q₀₀.sourceEdge ≠ C.q₁₀.sourceEdge ∧
    C.q₀₀.sourceEdge.1 = p.mate C.q₁₀.sourceEdge.1) ∨
  (C.q₀₀.sourceEdge ≠ C.q₁₁.sourceEdge ∧
    C.q₀₀.sourceEdge.1 = p.mate C.q₁₁.sourceEdge.1) ∨
  (C.q₀₁.sourceEdge ≠ C.q₁₀.sourceEdge ∧
    C.q₀₁.sourceEdge.1 = p.mate C.q₁₀.sourceEdge.1) ∨
  (C.q₀₁.sourceEdge ≠ C.q₁₁.sourceEdge ∧
    C.q₀₁.sourceEdge.1 = p.mate C.q₁₁.sourceEdge.1) ∨
  (C.q₁₀.sourceEdge ≠ C.q₁₁.sourceEdge ∧
    C.q₁₀.sourceEdge.1 = p.mate C.q₁₁.sourceEdge.1)

/-- Every concrete cross block either saturates some owner branch with its
two internal matching edges, or contains two distinct edges owned by the two
branches of one root-mate pair. -/
theorem OneHighCrossBlockSourceConfiguration.saturatedOwner_or_mateCollision
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (C : OneHighCrossBlockSourceConfiguration G hfree hv p) :
    (∃ s : {z : V // z ∈ G.neighborSet v},
      oneHighFamilyInternalEdges p.profile (p.branchLabel s) = 2) ∨
      OneHighCrossBlockMateOwnerCollision G hfree hv p C := by
  have saturated {a b : {z : V // z ∈ G.neighborSet v}}
      (q : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
        p.outer_degree p.mate p.mate_adj a b)
      {c d : {z : V // z ∈ G.neighborSet v}}
      (r : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
        p.outer_degree p.mate p.mate_adj c d)
      (hne : q.sourceEdge ≠ r.sourceEdge)
      (howner : q.sourceEdge.1 = r.sourceEdge.1) :
      ∃ s : {z : V // z ∈ G.neighborSet v},
        oneHighFamilyInternalEdges p.profile (p.branchLabel s) = 2 := by
    refine ⟨q.sourceEdge.1, ?_⟩
    apply oneHighFamilyInternalEdges_eq_two_of_distinct_sources_sameOwner
      G hfree hv p
    · simpa [nonconstantMatchingEdgeSources, Function.comp_def] using
        q.sourceEdge_mem
    · simpa [nonconstantMatchingEdgeSources, Function.comp_def] using
        r.sourceEdge_mem
    · exact hne
    · exact howner
  rcases C.distinct_same_or_mate_collision G hfree hv p with
    ⟨hne, hsame | hmate⟩ | ⟨hne, hsame | hmate⟩ |
    ⟨hne, hsame | hmate⟩ | ⟨hne, hsame | hmate⟩ |
    ⟨hne, hsame | hmate⟩ | ⟨hne, hsame | hmate⟩
  · exact Or.inl (saturated C.q₀₀ C.q₀₁ hne hsame)
  · exact Or.inr (Or.inl ⟨hne, hmate⟩)
  · exact Or.inl (saturated C.q₀₀ C.q₁₀ hne hsame)
  · exact Or.inr (Or.inr (Or.inl ⟨hne, hmate⟩))
  · exact Or.inl (saturated C.q₀₀ C.q₁₁ hne hsame)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, hmate⟩)))
  · exact Or.inl (saturated C.q₀₁ C.q₁₀ hne hsame)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, hmate⟩))))
  · exact Or.inl (saturated C.q₀₁ C.q₁₁ hne hsame)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hne, hmate⟩)))))
  · exact Or.inl (saturated C.q₁₀ C.q₁₁ hne hsame)
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hne, hmate⟩)))))

/-- At least one of the four concrete cross-block edges is owned by a
two-edge branch.  Same-owner collisions force this by capacity; mate-owner
collisions force it by the canonical profile symmetry of a mate pair. -/
theorem OneHighCrossBlockSourceConfiguration.has_saturated_sourceEdge
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (C : OneHighCrossBlockSourceConfiguration G hfree hv p) :
    oneHighFamilyInternalEdges p.profile
        (p.branchLabel C.q₀₀.sourceEdge.1) = 2 ∨
      oneHighFamilyInternalEdges p.profile
        (p.branchLabel C.q₀₁.sourceEdge.1) = 2 ∨
      oneHighFamilyInternalEdges p.profile
        (p.branchLabel C.q₁₀.sourceEdge.1) = 2 ∨
      oneHighFamilyInternalEdges p.profile
        (p.branchLabel C.q₁₁.sourceEdge.1) = 2 := by
  have same {a b : {z : V // z ∈ G.neighborSet v}}
      (q : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
        p.outer_degree p.mate p.mate_adj a b)
      {c d : {z : V // z ∈ G.neighborSet v}}
      (r : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
        p.outer_degree p.mate p.mate_adj c d)
      (hne : q.sourceEdge ≠ r.sourceEdge)
      (howner : q.sourceEdge.1 = r.sourceEdge.1) :
      oneHighFamilyInternalEdges p.profile
        (p.branchLabel q.sourceEdge.1) = 2 := by
    apply oneHighFamilyInternalEdges_eq_two_of_distinct_sources_sameOwner
      G hfree hv p
    · simpa [nonconstantMatchingEdgeSources, Function.comp_def] using
        q.sourceEdge_mem
    · simpa [nonconstantMatchingEdgeSources, Function.comp_def] using
        r.sourceEdge_mem
    · exact hne
    · exact howner
  have mate {a b : {z : V // z ∈ G.neighborSet v}}
      (q : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
        p.outer_degree p.mate p.mate_adj a b)
      {c d : {z : V // z ∈ G.neighborSet v}}
      (r : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
        p.outer_degree p.mate p.mate_adj c d)
      (howner : q.sourceEdge.1 = p.mate r.sourceEdge.1) :
      oneHighFamilyInternalEdges p.profile
          (p.branchLabel q.sourceEdge.1) = 2 ∨
        oneHighFamilyInternalEdges p.profile
          (p.branchLabel r.sourceEdge.1) = 2 := by
    rcases oneHighFamilyInternalEdges_eq_two_or_mate_eq_two p.profile
        (p.branchLabel r.sourceEdge.1) with hr | hmate
    · exact Or.inr hr
    · left
      have hlabel : p.branchLabel q.sourceEdge.1 =
          oneHighStandardMate (p.branchLabel r.sourceEdge.1) := by
        rw [howner, p.branch_mate]
      rwa [hlabel]
  rcases C.distinct_same_or_mate_collision G hfree hv p with
    ⟨hne, hsame | hmate⟩ | ⟨hne, hsame | hmate⟩ |
    ⟨hne, hsame | hmate⟩ | ⟨hne, hsame | hmate⟩ |
    ⟨hne, hsame | hmate⟩ | ⟨hne, hsame | hmate⟩
  · exact Or.inl (same C.q₀₀ C.q₀₁ hne hsame)
  · rcases mate C.q₀₀ C.q₀₁ hmate with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inl (same C.q₀₀ C.q₁₀ hne hsame)
  · rcases mate C.q₀₀ C.q₁₀ hmate with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inl (same C.q₀₀ C.q₁₁ hne hsame)
  · rcases mate C.q₀₀ C.q₁₁ hmate with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inl (same C.q₀₁ C.q₁₀ hne hsame))
  · rcases mate C.q₀₁ C.q₁₀ hmate with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl (same C.q₀₁ C.q₁₁ hne hsame))
  · rcases mate C.q₀₁ C.q₁₁ hmate with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inr (Or.inl
      (same C.q₁₀ C.q₁₁ hne hsame)))
  · rcases mate C.q₁₀ C.q₁₁ hmate with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

/-- A concrete cross block therefore determines an exact length-two
executable source row together with one of its actual canonical miss pairs. -/
theorem OneHighCrossBlockSourceConfiguration.exists_saturatedSourcePairingWitness
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (C : OneHighCrossBlockSourceConfiguration G hfree hv p) :
    Nonempty (OneHighSaturatedCrossSourcePairingWitness G hfree hv p) := by
  have make {a b : {z : V // z ∈ G.neighborSet v}}
      (q : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
        p.outer_degree p.mate p.mate_adj a b)
      (hs : oneHighFamilyInternalEdges p.profile
        (p.branchLabel q.sourceEdge.1) = 2) :
      Nonempty (OneHighSaturatedCrossSourcePairingWitness G hfree hv p) := by
    refine ⟨{
      a := a
      b := b
      q := q
      saturated := hs
      pair_mem := q.canonicalPair_mem_graphSourcePairing G hfree hv p
      row_length := ?_ }⟩
    calc
      (oneHighGraphSourcePairing G hfree hv p
          (p.branchLabel q.sourceEdge.1)).length =
          oneHighFamilyInternalEdges p.profile
            (p.branchLabel q.sourceEdge.1) :=
        oneHighGraphSourcePairing_length G hfree hv p _
      _ = 2 := hs
  rcases C.has_saturated_sourceEdge G hfree hv p with h | h | h | h
  · exact make C.q₀₀ h
  · exact make C.q₀₁ h
  · exact make C.q₁₀ h
  · exact make C.q₁₁ h

/-- Row-reconstruction form: an owner of one concrete cross-block source
edge has exactly four matched vertices, hence its two internal edges exhaust
the branch matching. -/
theorem OneHighCrossBlockSourceConfiguration.has_full_matched_sourceBranch
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (C : OneHighCrossBlockSourceConfiguration G hfree hv p) :
    Fintype.card (OneHighMatchedBranchVertices G v C.q₀₀.sourceEdge.1) = 4 ∨
      Fintype.card (OneHighMatchedBranchVertices G v C.q₀₁.sourceEdge.1) = 4 ∨
      Fintype.card (OneHighMatchedBranchVertices G v C.q₁₀.sourceEdge.1) = 4 ∨
      Fintype.card (OneHighMatchedBranchVertices G v C.q₁₁.sourceEdge.1) = 4 := by
  have full (s : {z : V // z ∈ G.neighborSet v})
      (hs : oneHighFamilyInternalEdges p.profile (p.branchLabel s) = 2) :
      Fintype.card (OneHighMatchedBranchVertices G v s) = 4 := by
    rw [card_oneHighMatchedBranchVertices_eq_highBranchMatchedCount]
    have hmatched := p.matched_count (p.branchLabel s)
    simpa [hs] using hmatched
  rcases C.has_saturated_sourceEdge G hfree hv p with h | h | h | h
  · exact Or.inl (full C.q₀₀.sourceEdge.1 h)
  · exact Or.inr (Or.inl (full C.q₀₁.sourceEdge.1 h))
  · exact Or.inr (Or.inr (Or.inl (full C.q₁₀.sourceEdge.1 h)))
  · exact Or.inr (Or.inr (Or.inr (full C.q₁₁.sourceEdge.1 h)))

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
