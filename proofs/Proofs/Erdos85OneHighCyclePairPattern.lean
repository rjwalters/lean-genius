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

theorem exists_threeColor_turn_fin3
    {C : Type*} (color : Fin 3 → C)
    (hadj : ∀ i, color i ≠ color (i + 1)) :
    ∃ i, color i ≠ color (i + 1) ∧
      color (i + 1) ≠ color (i + 1 + 1) ∧
      color i ≠ color (i + 1 + 1) := by
  rcases exists_threeColor_turn_or_twoStepPeriodic
    (fun i : Fin 3 => i + 1) color hadj with h | h
  · simpa [add_assoc] using h
  · have h0 := h (0 : Fin 3)
    have h2 := h (2 : Fin 3)
    norm_num [Fin.add_def] at h0 h2
    exfalso
    exact (hadj 0) (h0.trans h2)

theorem exists_threeColor_turn_fin5
    {C : Type*} (color : Fin 5 → C)
    (hadj : ∀ i, color i ≠ color (i + 1)) :
    ∃ i, color i ≠ color (i + 1) ∧
      color (i + 1) ≠ color (i + 1 + 1) ∧
      color i ≠ color (i + 1 + 1) := by
  rcases exists_threeColor_turn_or_twoStepPeriodic
    (fun i : Fin 5 => i + 1) color hadj with h | h
  · simpa [add_assoc] using h
  · have h0 := h (0 : Fin 5)
    have h2 := h (2 : Fin 5)
    have h4 := h (4 : Fin 5)
    norm_num [Fin.add_def] at h0 h2 h4
    exfalso
    exact (hadj 0) (h0.trans (h2.trans h4))

theorem exists_threeColor_turn_fin7
    {C : Type*} (color : Fin 7 → C)
    (hadj : ∀ i, color i ≠ color (i + 1)) :
    ∃ i, color i ≠ color (i + 1) ∧
      color (i + 1) ≠ color (i + 1 + 1) ∧
      color i ≠ color (i + 1 + 1) := by
  rcases exists_threeColor_turn_or_twoStepPeriodic
    (fun i : Fin 7 => i + 1) color hadj with h | h
  · simpa [add_assoc] using h
  · have h0 := h (0 : Fin 7)
    have h2 := h (2 : Fin 7)
    have h4 := h (4 : Fin 7)
    have h6 := h (6 : Fin 7)
    norm_num [Fin.add_def] at h0 h2 h4 h6
    exfalso
    exact (hadj 0) (h0.trans (h2.trans (h4.trans h6)))

/-- Every odd-length H1 root-pair cycle (length 3, 5, or 7) has a turn
through three distinct mate-pairs. -/
theorem exists_threeRootPair_turn_fin3
    (label : Fin 3 → Fin 8)
    (hadj : ∀ i, oneHighRootPair (label i) ≠
      oneHighRootPair (label (i + 1))) :
    ∃ i, oneHighRootPair (label i) ≠ oneHighRootPair (label (i + 1)) ∧
      oneHighRootPair (label (i + 1)) ≠
        oneHighRootPair (label (i + 1 + 1)) ∧
      oneHighRootPair (label i) ≠
        oneHighRootPair (label (i + 1 + 1)) :=
  exists_threeColor_turn_fin3 (fun i => oneHighRootPair (label i)) hadj

theorem exists_threeRootPair_turn_fin5
    (label : Fin 5 → Fin 8)
    (hadj : ∀ i, oneHighRootPair (label i) ≠
      oneHighRootPair (label (i + 1))) :
    ∃ i, oneHighRootPair (label i) ≠ oneHighRootPair (label (i + 1)) ∧
      oneHighRootPair (label (i + 1)) ≠
        oneHighRootPair (label (i + 1 + 1)) ∧
      oneHighRootPair (label i) ≠
        oneHighRootPair (label (i + 1 + 1)) :=
  exists_threeColor_turn_fin5 (fun i => oneHighRootPair (label i)) hadj

theorem exists_threeRootPair_turn_fin7
    (label : Fin 7 → Fin 8)
    (hadj : ∀ i, oneHighRootPair (label i) ≠
      oneHighRootPair (label (i + 1))) :
    ∃ i, oneHighRootPair (label i) ≠ oneHighRootPair (label (i + 1)) ∧
      oneHighRootPair (label (i + 1)) ≠
        oneHighRootPair (label (i + 1 + 1)) ∧
      oneHighRootPair (label i) ≠
        oneHighRootPair (label (i + 1 + 1)) :=
  exists_threeColor_turn_fin7 (fun i => oneHighRootPair (label i)) hadj

end

end Erdos85
