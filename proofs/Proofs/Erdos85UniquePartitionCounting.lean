import Proofs.Erdos85MixedAnchorComponentPartition

/-!
# Counting a uniquely indexed finite partition

This small combinatorial bridge turns the unique component assignment from
the mixed-anchor geometry into a sum of per-component fiber cardinalities.
-/

namespace Erdos85

noncomputable section

/-- If every element of `T` satisfies exactly one predicate indexed by a
member of `S`, then `T` is counted by the sum of the corresponding filtered
cardinalities. -/
theorem card_eq_sum_card_filter_of_existsUnique_mem
    {C X : Type*} [DecidableEq C] [DecidableEq X]
    (S : Finset C) (T : Finset X) (P : C → X → Prop) [DecidableRel P]
    (hunique : ∀ x ∈ T, ∃! c, c ∈ S ∧ P c x) :
    T.card = ∑ c ∈ S, (T.filter (P c)).card := by
  classical
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨c, hc, hcuniq⟩ := hunique x hx
  have hothers : ∀ e ∈ S, e ≠ c → ¬P e x := by
    intro e he hec heP
    exact hec (hcuniq e ⟨he, heP⟩)
  symm
  calc
    ∑ e ∈ S, (if P e x then 1 else 0) =
        (if P c x then 1 else 0) := by
      apply Finset.sum_eq_single c
      · intro e he hec
        simp [hothers e he hec]
      · intro hcnot
        exact absurd hc.1 hcnot
    _ = 1 := if_pos hc.2

end

end Erdos85
