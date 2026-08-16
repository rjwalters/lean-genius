import Proofs.Erdos85MatchingMultiplicityRelabel
import Proofs.Erdos85OneHighStructuralTerminalInterface
import Proofs.Erdos85OneHighOddLabelTurn

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
