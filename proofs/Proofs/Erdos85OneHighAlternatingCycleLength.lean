import Proofs.Erdos85OneHighOddLabelCyclePairSectors

/-! # Length of the alternating mate-pair residual -/

namespace Erdos85

open SimpleGraph

noncomputable section

/-- A genuine cycle on the eight canonical root labels whose adjacent pair
colors differ and whose pair colors repeat every two darts has length four.
Longer cycles would contain three distinct labels in one two-element pair
fiber. -/
theorem oneHigh_oddLabelCycle_length_eq_four_of_twoStepPeriodic
    {L : Type*} [Fintype L] [DecidableEq L]
    (branchLabel : L ≃ Fin 8)
    {H : SimpleGraph L} {l : L} (c : H.Walk l l) (hc : c.IsCycle)
    (hproper : ∀ i : Fin c.length,
      oneHighRootPair (branchLabel (c.getVert i.1)) ≠
        oneHighRootPair
          (branchLabel (c.getVert (oneHighCycleNext c hc i).1)))
    (hperiodic : ∀ i : Fin c.length,
      oneHighRootPair (branchLabel (c.getVert i.1)) =
        oneHighRootPair (branchLabel (c.getVert
          (oneHighCycleNext c hc (oneHighCycleNext c hc i)).1))) :
    c.length = 4 := by
  have hcard : Fintype.card L = 8 := by
    simpa using Fintype.card_congr branchLabel
  have hlo : 3 ≤ c.length := hc.three_le_length
  have hhi : c.length ≤ 8 := by
    have := IsCycle.length_le_fintype_card hc
    simpa [hcard] using this
  have hcases : c.length = 3 ∨ c.length = 4 ∨ c.length = 5 ∨
      c.length = 6 ∨ c.length = 7 ∨ c.length = 8 := by
    omega
  rcases hcases with hlen | hlen | hlen | hlen | hlen | hlen
  · have hp := hperiodic (⟨1, by omega⟩ : Fin c.length)
    have hn := hproper (⟨0, by omega⟩ : Fin c.length)
    simp [oneHighCycleNext, hlen] at hp hn
    exact (hn hp.symm).elim
  · exact hlen
  all_goals
    have h02 := hperiodic (⟨0, by omega⟩ : Fin c.length)
    have h24 := hperiodic (⟨2, by omega⟩ : Fin c.length)
    simp [oneHighCycleNext, hlen] at h02 h24
    have h02' : oneHighRootPair (branchLabel (c.getVert 0)) =
        oneHighRootPair (branchLabel (c.getVert 2)) := by simpa using h02
    have hthree := three_same_oneHighRootPair_not_pairwise_distinct
      (branchLabel (c.getVert 0))
      (branchLabel (c.getVert 2))
      (branchLabel (c.getVert 4)) h02' (h02'.trans h24)
    rcases hthree with heq | heq | heq
    · have hind : (0 : Nat) = 2 := hc.getVert_injOn'
        (show 0 ≤ c.length - 1 by omega)
        (show 2 ≤ c.length - 1 by omega)
        (branchLabel.injective heq)
      omega
    · have hind : (0 : Nat) = 4 := hc.getVert_injOn'
        (show 0 ≤ c.length - 1 by omega)
        (show 4 ≤ c.length - 1 by omega)
        (branchLabel.injective heq)
      omega
    · have hind : (2 : Nat) = 4 := hc.getVert_injOn'
        (show 2 ≤ c.length - 1 by omega)
        (show 4 ≤ c.length - 1 by omega)
        (branchLabel.injective heq)
      omega

end

end Erdos85
