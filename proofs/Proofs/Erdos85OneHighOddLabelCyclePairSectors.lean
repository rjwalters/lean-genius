import Proofs.Erdos85OneHighOddLabelCycleSources
import Proofs.Erdos85OneHighCyclePairPattern

/-! # Mate-pair sectors of an odd label cycle

A genuine label cycle first splits according to whether one of its edges lies
inside a root mate-pair.  In the complementary proper pair-color sector, the
cycle either has a three-distinct-pair turn or is two-step periodic.
-/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- Exact three-way pair-pattern split for a genuine root-label cycle. -/
theorem oneHigh_oddLabelCycle_pairPattern_trichotomy
    {L : Type*} [Fintype L] [DecidableEq L]
    (branchLabel : L ≃ Fin 8)
    {H : SimpleGraph L} {l : L} (c : H.Walk l l) (hc : c.IsCycle) :
    (∃ i : Fin c.length,
      oneHighRootPair (branchLabel (c.getVert i.1)) =
        oneHighRootPair
          (branchLabel (c.getVert (oneHighCycleNext c hc i).1))) ∨
    (∃ i : Fin c.length,
      oneHighRootPair (branchLabel (c.getVert i.1)) ≠
        oneHighRootPair
          (branchLabel (c.getVert (oneHighCycleNext c hc i).1)) ∧
      oneHighRootPair
          (branchLabel (c.getVert (oneHighCycleNext c hc i).1)) ≠
        oneHighRootPair (branchLabel (c.getVert
          (oneHighCycleNext c hc (oneHighCycleNext c hc i)).1)) ∧
      oneHighRootPair (branchLabel (c.getVert i.1)) ≠
        oneHighRootPair (branchLabel (c.getVert
          (oneHighCycleNext c hc (oneHighCycleNext c hc i)).1))) ∨
    ((∀ i : Fin c.length,
      oneHighRootPair (branchLabel (c.getVert i.1)) ≠
        oneHighRootPair
          (branchLabel (c.getVert (oneHighCycleNext c hc i).1))) ∧
     ∀ i : Fin c.length,
       oneHighRootPair (branchLabel (c.getVert i.1)) =
         oneHighRootPair (branchLabel (c.getVert
           (oneHighCycleNext c hc (oneHighCycleNext c hc i)).1))) := by
  classical
  let next := oneHighCycleNext c hc
  let label : Fin c.length → Fin 8 := fun i => branchLabel (c.getVert i.1)
  by_cases hproper : ∀ i, oneHighRootPair (label i) ≠
      oneHighRootPair (label (next i))
  · rcases exists_threeRootPair_turn_or_twoStepPeriodic next label hproper with
      hturn | hperiodic
    · exact Or.inr (Or.inl hturn)
    · exact Or.inr (Or.inr ⟨hproper, hperiodic⟩)
  · push Not at hproper
    obtain ⟨i, hi⟩ := hproper
    exact Or.inl ⟨i, hi⟩

end

end Erdos85
