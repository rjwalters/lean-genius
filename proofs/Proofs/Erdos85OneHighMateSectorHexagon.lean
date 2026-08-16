import Proofs.Erdos85OneHighMateEdgeCycleHexagon
import Proofs.Erdos85OneHighOddLabelSectorCapstone

/-! # Replace the mate-edge odd-label sector by a graph hexagon -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- The mate-edge branch of the unconditional odd-label cycle split carries
an actual mate-miss hexagon.  Only the genuinely unresolved three-pair-turn
and alternating four-cycle sectors remain. -/
theorem oneHigh_even_multiplicities_or_mateMissHexagon_or_residualCycle
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
    (branchLabel : {z : V // z ∈ G.neighborSet v} ≃ Fin 8)
    (hbranchMate : ∀ s, branchLabel (rootMate s) =
      oneHighStandardMate (branchLabel s)) :
    let mate := oneHighGlobalInternalMate G hfree v
    let label := oneHighGlobalMissLabel G hfree hv hexternal houterDegree
      rootMate hrootAdj
    let m := exchangedMissPairMultiplicity mate label
    (∀ k ∈ exchangedMissPairKeys {z : V // z ∈ G.neighborSet v}, Even (m k)) ∨
      Nonempty (OneHighMateMissHexagon G v) ∨
      ∃ l, ∃ c : (oddExchangedKeyLabelGraph m).Walk l l,
        ∃ hc : c.IsCycle,
          ((∃ i : Fin c.length,
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
  rcases oneHigh_even_multiplicities_or_oddLabel_cycle_sectors
      G hfree hv hneigh hlocal hexternal houterDegree rootMate hrootAdj
      hrootInv branchLabel with hall | ⟨l, c, hc, hsector⟩
  · exact Or.inl hall
  · rcases hsector with hmate | hturn | halt
    · obtain ⟨i, hpair⟩ := hmate
      exact Or.inr (Or.inl
        (exists_oneHighMateMissHexagon_of_oddLabelCycle_mateEdge
          G hfree hv hexternal houterDegree rootMate hrootAdj branchLabel
          hbranchMate hc i hpair))
    · exact Or.inr (Or.inr ⟨l, c, hc, Or.inl hturn⟩)
    · exact Or.inr (Or.inr ⟨l, c, hc, Or.inr halt⟩)

end

end Erdos85
