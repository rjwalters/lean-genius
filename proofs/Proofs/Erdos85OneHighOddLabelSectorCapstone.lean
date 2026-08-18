import Proofs.Erdos85OneHighAlternatingCycleLength
import Proofs.Erdos85OneHighOddCycleBridge

/-! # Complete pair-sector split for an odd exchanged-label cycle -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Under the one-high graph hypotheses, either every exchanged miss-pair
multiplicity is even, or a genuine odd-support label cycle lies in one of the
three exhaustive root-pair sectors.  In the periodic residual its length is
forced to be four. -/
theorem oneHigh_even_multiplicities_or_oddLabel_cycle_sectors
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (hv : G.degree v = 8)
    (hneigh : ∀ y, G.Adj v y → G.degree y = 7)
    (hlocal : ∀ u : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree u = 1)
    (hexternal : externalRepairCandidates G v = ∅)
    (houterDegree : ∀ {a : V}, a ∈ secondLayer G v → G.degree a = 7)
    (rootMate : {z : V // z ∈ G.neighborSet v} →
      {z : V // z ∈ G.neighborSet v})
    (hrootAdj : ∀ s, G.Adj s.1 (rootMate s).1)
    (hrootInv : Function.Involutive rootMate)
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8) :
    let mate := oneHighGlobalInternalMate G hfree v
    let label := oneHighGlobalMissLabel G hfree hv hexternal houterDegree
      rootMate hrootAdj
    let m := exchangedMissPairMultiplicity mate label
    (∀ k ∈ exchangedMissPairKeys {z : V // z ∈ G.neighborSet v}, Even (m k)) ∨
      ∃ l, ∃ c : (oddExchangedKeyLabelGraph m).Walk l l,
        ∃ hc : c.IsCycle,
          ((∃ i : Fin c.length,
              oneHighRootPair (branchLabel (c.getVert i.1)) =
                oneHighRootPair (branchLabel
                  (c.getVert (oneHighCycleNext c hc i).1))) ∨
           (∃ i : Fin c.length,
              oneHighRootPair (branchLabel (c.getVert i.1)) ≠
                oneHighRootPair (branchLabel
                  (c.getVert (oneHighCycleNext c hc i).1)) ∧
              oneHighRootPair (branchLabel
                  (c.getVert (oneHighCycleNext c hc i).1)) ≠
                oneHighRootPair (branchLabel (c.getVert
                  (oneHighCycleNext c hc
                    (oneHighCycleNext c hc i)).1)) ∧
              oneHighRootPair (branchLabel (c.getVert i.1)) ≠
                oneHighRootPair (branchLabel (c.getVert
                  (oneHighCycleNext c hc
                    (oneHighCycleNext c hc i)).1))) ∨
           (c.length = 4 ∧
             (∀ i : Fin c.length,
                oneHighRootPair (branchLabel (c.getVert i.1)) ≠
                  oneHighRootPair (branchLabel
                    (c.getVert (oneHighCycleNext c hc i).1))) ∧
             ∀ i : Fin c.length,
                oneHighRootPair (branchLabel (c.getVert i.1)) =
                  oneHighRootPair (branchLabel (c.getVert
                    (oneHighCycleNext c hc
                      (oneHighCycleNext c hc i)).1)))) := by
  classical
  dsimp only
  obtain hall | ⟨l, c, hc⟩ := oneHigh_even_multiplicities_or_oddLabel_cycle
    G hfree hv hneigh hlocal hexternal houterDegree rootMate hrootAdj hrootInv
  · exact Or.inl hall
  · right
    refine ⟨l, c, hc, ?_⟩
    rcases oneHigh_oddLabelCycle_pairPattern_trichotomy branchLabel c hc with
      hmate | hturn | ⟨hproper, hperiodic⟩
    · exact Or.inl hmate
    · exact Or.inr (Or.inl hturn)
    · exact Or.inr (Or.inr ⟨
        oneHigh_oddLabelCycle_length_eq_four_of_twoStepPeriodic
          branchLabel c hc hproper hperiodic,
        hproper, hperiodic⟩)

end

end Erdos85
