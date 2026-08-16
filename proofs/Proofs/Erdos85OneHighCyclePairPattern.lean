import Proofs.Erdos85OneHighSourcePairTurn

/-! # Mate-pair patterns along a genuine label cycle -/

namespace Erdos85

noncomputable section

/-- A proper coloring along any successor map either has a turn using three
distinct colors or repeats after two successor steps.  On a cycle, the latter
is precisely the alternating two-color residual. -/
theorem exists_threeColor_turn_or_twoStepPeriodic
    {I C : Type*} (next : I → I) (color : I → C)
    (hadj : ∀ i, color i ≠ color (next i)) :
    (∃ i, color i ≠ color (next i) ∧
      color (next i) ≠ color (next (next i)) ∧
      color i ≠ color (next (next i))) ∨
      ∀ i, color i = color (next (next i)) := by
  by_cases hturn : ∃ i, color i ≠ color (next i) ∧
      color (next i) ≠ color (next (next i)) ∧
      color i ≠ color (next (next i))
  · exact Or.inl hturn
  · right
    intro i
    by_contra hne
    apply hturn
    exact ⟨i, hadj i, hadj (next i), hne⟩

/-- Canonical root-pair specialization for a sequence of the eight H1 root
labels. -/
theorem exists_threeRootPair_turn_or_twoStepPeriodic
    {I : Type*} (next : I → I) (label : I → Fin 8)
    (hadj : ∀ i,
      oneHighRootPair (label i) ≠ oneHighRootPair (label (next i))) :
    (∃ i,
      oneHighRootPair (label i) ≠ oneHighRootPair (label (next i)) ∧
      oneHighRootPair (label (next i)) ≠
        oneHighRootPair (label (next (next i))) ∧
      oneHighRootPair (label i) ≠
        oneHighRootPair (label (next (next i)))) ∨
      ∀ i, oneHighRootPair (label i) =
        oneHighRootPair (label (next (next i))) := by
  exact exists_threeColor_turn_or_twoStepPeriodic next
    (fun i => oneHighRootPair (label i)) hadj

/-- Negating the three-pair turn alternative exposes the rigid alternating
residual directly. -/
theorem twoStepPeriodic_of_no_threeRootPair_turn
    {I : Type*} (next : I → I) (label : I → Fin 8)
    (hadj : ∀ i,
      oneHighRootPair (label i) ≠ oneHighRootPair (label (next i)))
    (hno : ¬ ∃ i,
      oneHighRootPair (label i) ≠ oneHighRootPair (label (next i)) ∧
      oneHighRootPair (label (next i)) ≠
        oneHighRootPair (label (next (next i))) ∧
      oneHighRootPair (label i) ≠
        oneHighRootPair (label (next (next i)))) :
    ∀ i, oneHighRootPair (label i) =
      oneHighRootPair (label (next (next i))) := by
  rcases exists_threeRootPair_turn_or_twoStepPeriodic next label hadj with h | h
  · exact (hno h).elim
  · exact h

end

end Erdos85
