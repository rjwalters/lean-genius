import Proofs.Erdos85MatchingMultiplicityRelabel
import Proofs.Erdos85OneHighStructuralTerminalInterface
import Proofs.Erdos85OneHighOddLabelTurn
import Proofs.Erdos85OneHighRootPairGraphDecoder

/-! # Concrete graph witnesses from the three-pair turn sector -/

namespace Erdos85

open SimpleGraph

noncomputable section

private theorem consecutive_minMax_ne
    {L : Type*} [LinearOrder L] {a b c : L}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    (min a b, max a b) ≠ (min b c, max b c) := by
  intro hpair
  rcases le_total a b with habLe | hbaLe <;>
    rcases le_total b c with hbcLe | hcbLe
  · rw [min_eq_left habLe, max_eq_right habLe,
      min_eq_left hbcLe, max_eq_right hbcLe] at hpair
    exact hab (Prod.mk.inj hpair).1
  · rw [min_eq_left habLe, max_eq_right habLe,
      min_eq_right hcbLe, max_eq_left hcbLe] at hpair
    exact hac (Prod.mk.inj hpair).1
  · rw [min_eq_right hbaLe, max_eq_left hbaLe,
      min_eq_left hbcLe, max_eq_right hbcLe] at hpair
    exact hac (Prod.mk.inj hpair).2
  · rw [min_eq_right hbaLe, max_eq_left hbaLe,
      min_eq_right hcbLe, max_eq_left hcbLe] at hpair
    exact hbc (Prod.mk.inj hpair).1

/-- The relabeled three-pair turn supplied by the structural capstone pulls
back to two genuine odd root-label edges.  Hence it has two concrete internal
matching-edge sources satisfying the exact source-pair trichotomy. -/
theorem exists_oneHighThreePairTurn_sourcePair_trichotomy
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (hturn : OneHighOddSupportThreePairTurnProp
      (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)))) :
    ∃ a b c : {z : V // z ∈ G.neighborSet v},
      oneHighRootPair (p.branchLabel a) ≠ oneHighRootPair (p.branchLabel b) ∧
      oneHighRootPair (p.branchLabel b) ≠ oneHighRootPair (p.branchLabel c) ∧
      oneHighRootPair (p.branchLabel a) ≠ oneHighRootPair (p.branchLabel c) ∧
      ∃ qAB : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
          p.outer_degree p.mate p.mate_adj a b,
        ∃ qBC : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
            p.outer_degree p.mate p.mate_adj b c,
          oneHighRootPair (p.branchLabel qAB.sourceEdge.1) =
              oneHighRootPair (p.branchLabel qBC.sourceEdge.1) ∨
            oneHighRootPair (p.branchLabel qAB.sourceEdge.1) =
              oneHighRootPair (p.branchLabel c) ∨
            oneHighRootPair (p.branchLabel qBC.sourceEdge.1) =
              oneHighRootPair (p.branchLabel a) := by
  obtain ⟨la, lb, lc, hab, hbc, hac, hAB, hBC⟩ := hturn
  let a := p.branchLabel.symm la
  let b := p.branchLabel.symm lb
  let c := p.branchLabel.symm lc
  have hlabels : p.branchLabel a = la ∧ p.branchLabel b = lb ∧
      p.branchLabel c = lc := by simp [a, b, c]
  have hadj (x y : {z : V // z ∈ G.neighborSet v})
      (hxy : (oddExchangedKeyLabelGraph
        (exchangedMissPairMultiplicity
          (oneHighGlobalInternalMate G hfree v)
          (fun z => p.branchLabel
            (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
              p.mate p.mate_adj z)))).Adj (p.branchLabel x) (p.branchLabel y)) :
      (oddExchangedKeyLabelGraph
        (exchangedMissPairMultiplicity
          (oneHighGlobalInternalMate G hfree v)
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj))).Adj x y := by
    refine ⟨fun h => hxy.1 (congrArg p.branchLabel h), ?_⟩
    rw [← exchangedMissPairMultiplicity_equiv
      (oneHighGlobalInternalMate G hfree v)
      (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
        p.mate p.mate_adj) p.branchLabel x y]
    simpa [Function.comp_def] using hxy.2
  have hAB' := hadj a b (by simpa [hlabels.1, hlabels.2.1] using hAB)
  have hBC' := hadj b c (by simpa [hlabels.2.1, hlabels.2.2] using hBC)
  obtain ⟨qAB, qBC, hsources⟩ :=
    exists_oneHighOddLabelTurn_sourcePair_trichotomy G hfree hv
      p.external_empty p.outer_degree p.mate p.mate_adj p.branchLabel
      p.branch_mate (by simpa [hlabels.1, hlabels.2.1] using hab)
      (by simpa [hlabels.2.1, hlabels.2.2] using hbc)
      (by simpa [hlabels.1, hlabels.2.2] using hac) hAB' hBC'
  exact ⟨a, b, c,
    by simpa [hlabels.1, hlabels.2.1] using hab,
    by simpa [hlabels.2.1, hlabels.2.2] using hbc,
    by simpa [hlabels.1, hlabels.2.2] using hac,
    qAB, qBC, hsources⟩

/-- A graph-level normal form for the residual three-pair-turn terminal.  It
retains the actual roots and internal matching edges, rather than only their
relabelled odd multiplicities. -/
structure OneHighPinnedThreePairTurn
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) where
  a : {z : V // z ∈ G.neighborSet v}
  b : {z : V // z ∈ G.neighborSet v}
  c : {z : V // z ∈ G.neighborSet v}
  ab_pair_ne : oneHighRootPair (p.branchLabel a) ≠
    oneHighRootPair (p.branchLabel b)
  bc_pair_ne : oneHighRootPair (p.branchLabel b) ≠
    oneHighRootPair (p.branchLabel c)
  ac_pair_ne : oneHighRootPair (p.branchLabel a) ≠
    oneHighRootPair (p.branchLabel c)
  qAB : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj a b
  qBC : OneHighOddLabelEdgeSourceWitness G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj b c
  source_edges_ne : qAB.sourceEdge ≠ qBC.sourceEdge
  source_sector :
    oneHighRootPair (p.branchLabel qAB.sourceEdge.1) =
        oneHighRootPair (p.branchLabel qBC.sourceEdge.1) ∨
      oneHighRootPair (p.branchLabel qAB.sourceEdge.1) =
        oneHighRootPair (p.branchLabel c) ∨
      oneHighRootPair (p.branchLabel qBC.sourceEdge.1) =
        oneHighRootPair (p.branchLabel a)

/-- In the equal-source-color sector, that color is necessarily the fourth
root pair: it avoids all three root pairs at the turn. -/
theorem OneHighPinnedThreePairTurn.sharpened_source_sector
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (T : OneHighPinnedThreePairTurn G hfree hv p) :
    (oneHighRootPair (p.branchLabel T.qAB.sourceEdge.1) =
        oneHighRootPair (p.branchLabel T.qBC.sourceEdge.1) ∧
      oneHighRootPair (p.branchLabel T.qAB.sourceEdge.1) ≠
        oneHighRootPair (p.branchLabel T.a) ∧
      oneHighRootPair (p.branchLabel T.qAB.sourceEdge.1) ≠
        oneHighRootPair (p.branchLabel T.b) ∧
      oneHighRootPair (p.branchLabel T.qAB.sourceEdge.1) ≠
        oneHighRootPair (p.branchLabel T.c)) ∨
      oneHighRootPair (p.branchLabel T.qAB.sourceEdge.1) =
        oneHighRootPair (p.branchLabel T.c) ∨
      oneHighRootPair (p.branchLabel T.qBC.sourceEdge.1) =
        oneHighRootPair (p.branchLabel T.a) := by
  rcases T.source_sector with hsame | hc | ha
  · left
    refine ⟨hsame, ?_, ?_, ?_⟩
    · exact oneHighRootPair_ne_of_branch_mem_far p.mate p.branchLabel
        p.branch_mate T.qAB.sourceEdge.1 T.a T.qAB.left_far
    · exact oneHighRootPair_ne_of_branch_mem_far p.mate p.branchLabel
        p.branch_mate T.qAB.sourceEdge.1 T.b T.qAB.right_far
    · intro heq
      exact (oneHighRootPair_ne_of_branch_mem_far p.mate p.branchLabel
        p.branch_mate T.qBC.sourceEdge.1 T.c T.qBC.right_far)
        (hsame.symm.trans heq)
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr ha)

/-- Equal source-pair color means that the two distinct matching edges are
owned either by the same root branch or by the two mate branches. -/
theorem OneHighPinnedThreePairTurn.equalColor_sourceBranches_eq_or_mate
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (T : OneHighPinnedThreePairTurn G hfree hv p)
    (hcolor : oneHighRootPair (p.branchLabel T.qAB.sourceEdge.1) =
      oneHighRootPair (p.branchLabel T.qBC.sourceEdge.1)) :
    T.qAB.sourceEdge.1 = T.qBC.sourceEdge.1 ∨
      T.qAB.sourceEdge.1 = p.mate T.qBC.sourceEdge.1 := by
  exact (oneHighRootPair_branchLabel_eq_iff_eq_or_rootMate
    p.mate p.branchLabel p.branch_mate _ _).mp hcolor

/-- Fully graph-decoded terminal split.  There is no remaining quotient-color
equality: the two turn edges are owned by one branch, by mate branches, or
one of the two edge sources is colored by the opposite turn endpoint pair. -/
theorem OneHighPinnedThreePairTurn.graph_source_sector
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (T : OneHighPinnedThreePairTurn G hfree hv p) :
    T.qAB.sourceEdge.1 = T.qBC.sourceEdge.1 ∨
      T.qAB.sourceEdge.1 = p.mate T.qBC.sourceEdge.1 ∨
      oneHighRootPair (p.branchLabel T.qAB.sourceEdge.1) =
        oneHighRootPair (p.branchLabel T.c) ∨
      oneHighRootPair (p.branchLabel T.qBC.sourceEdge.1) =
        oneHighRootPair (p.branchLabel T.a) := by
  rcases T.source_sector with hcolor | hc | ha
  · rcases T.equalColor_sourceBranches_eq_or_mate G hfree hv p hcolor with
      hsame | hmate
    · exact Or.inl hsame
    · exact Or.inr (Or.inl hmate)
  · exact Or.inr (Or.inr (Or.inl hc))
  · exact Or.inr (Or.inr (Or.inr ha))

/-- The exact graph-side obligation remaining after the multiplicity turn is
decoded into roots and matching-edge sources. -/
def OneHighPinnedThreePairTurnSectorExcluded : Prop :=
  ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
    (_ : DecidableRel (antipodalGraph G).Adj)
    (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
    (hfree : ¬ containsC4 (Fin 49) G) →
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x) →
    (hHigh : (orderFortyNineHighVertices G).card = 1) →
    ∀ {v : Fin 49} (hv : G.degree v = 8)
      (p : OneHighRawV2Presentation G hfree v),
      Nonempty (OneHighPinnedThreePairTurn G hfree hv p) → False

/-- Excluding the pinned source configuration excludes the original
three-pair-turn multiplicity sector. -/
theorem oneHighThreePairTurnSectorExcluded_of_pinned
    (h : OneHighPinnedThreePairTurnSectorExcluded) :
    OneHighThreePairTurnSectorExcluded := by
  intro G _ _ _ hfree hmin hHigh v hv p
  dsimp only
  intro hturn
  obtain ⟨a, b, c, hab, hbc, hac, qAB, qBC, hsources⟩ :=
    exists_oneHighThreePairTurn_sourcePair_trichotomy G hfree hv p hturn
  have habv : a ≠ b := fun e => hab (congrArg
    (fun x => oneHighRootPair (p.branchLabel x)) e)
  have hbcv : b ≠ c := fun e => hbc (congrArg
    (fun x => oneHighRootPair (p.branchLabel x)) e)
  have hacv : a ≠ c := fun e => hac (congrArg
    (fun x => oneHighRootPair (p.branchLabel x)) e)
  have hsourceNe : qAB.sourceEdge ≠ qBC.sourceEdge := by
    intro heq
    apply consecutive_minMax_ne habv hbcv hacv
    rw [← qAB.key_eq, ← qBC.key_eq, heq]
  exact h G inferInstance inferInstance inferInstance hfree hmin hHigh hv p
    ⟨⟨a, b, c, hab, hbc, hac, qAB, qBC, hsourceNe, hsources⟩⟩

end

end Erdos85
