import Proofs.Erdos85PoleOwnerFlipChannelDecomposition

/-!
# Pole-owner odd-cell obstruction

The pole identity supplies one unit distributed among four *labelled* source
channels.  Therefore a downstream endpoint ledger which cancels those sources
cell by cell cannot have all label fibres even.  This is the precise interface
obligation hidden by an aggregate pairing argument.
-/

namespace Erdos85

/-- Labels of the four source channels attached to one pole owner. -/
inductive PoleOwnerChannelLabel
  | inactiveSplit
  | inactiveK
  | flip00
  | flip11
deriving DecidableEq, Fintype

/-- The pole source value in a specified labelled channel. -/
def poleOwnerSourceAt (C : PoleOwnerFlipChannels) :
    PoleOwnerChannelLabel → ZMod 2
  | .inactiveSplit => C.inactiveSplit
  | .inactiveK => C.inactiveK
  | .flip00 => C.flip00
  | .flip11 => C.flip11

/-- The derived pole demand is odd across the four labelled cells. -/
theorem sum_poleOwnerSourceAt_eq_one
    (k sigma activity : ZMod 2) (hsource : k + sigma = 1) :
    ∑ label : PoleOwnerChannelLabel,
      poleOwnerSourceAt (poleOwnerFlipChannels k sigma activity) label = 1 := by
  have huniv : (Finset.univ : Finset PoleOwnerChannelLabel) =
      {.inactiveSplit, .inactiveK, .flip00, .flip11} := by
    ext label
    fin_cases label <;> simp
  rw [huniv]
  simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    reduceCtorEq, or_self, not_false_eq_true, Finset.sum_singleton,
    poleOwnerSourceAt]
  simpa [add_assoc] using
    (one_eq_sum_poleOwnerFlipChannels k sigma activity hsource).symm

/-- Over `F₂`, exact cellwise cancellation is equivalent to copying the
source parity into the correspondingly labelled downstream fibre. -/
theorem poleOwner_cellwise_cancel_iff
    (C : PoleOwnerFlipChannels)
    (downstream : PoleOwnerChannelLabel → ZMod 2) :
    (∀ label, poleOwnerSourceAt C label + downstream label = 0) ↔
      downstream = poleOwnerSourceAt C := by
  constructor
  · intro h
    funext label
    have hsum := h label
    rw [eq_neg_of_add_eq_zero_right hsum]
    generalize poleOwnerSourceAt C label = x
    fin_cases x <;> rfl
  · rintro rfl label
    have hchar : (2 : ZMod 2) = 0 := by decide
    rw [← two_mul, hchar, zero_mul]

/-- **Odd labelled-cell obstruction (`73rnz_cjibkn`).**  Any downstream
ledger which cancels the four pole sources label by label has odd aggregate
parity, and hence contains a nonzero labelled fibre. -/
theorem poleOwner_downstream_odd_of_cellwise_cancel
    (k sigma activity : ZMod 2) (hsource : k + sigma = 1)
    (downstream : PoleOwnerChannelLabel → ZMod 2)
    (hcancel : ∀ label,
      poleOwnerSourceAt (poleOwnerFlipChannels k sigma activity) label +
        downstream label = 0) :
    (∑ label, downstream label) = 1 ∧
      ∃ label, downstream label ≠ 0 := by
  have hdown : downstream =
      poleOwnerSourceAt (poleOwnerFlipChannels k sigma activity) :=
    (poleOwner_cellwise_cancel_iff _ downstream).mp hcancel
  constructor
  · rw [hdown]
    exact sum_poleOwnerSourceAt_eq_one k sigma activity hsource
  · by_contra hnone
    push Not at hnone
    have hsumZero : (∑ label, downstream label) = 0 := by
      apply Finset.sum_eq_zero
      intro label _
      exact hnone label
    have hsumOne : (∑ label, downstream label) = 1 := by
      rw [hdown]
      exact sum_poleOwnerSourceAt_eq_one k sigma activity hsource
    rw [hsumZero] at hsumOne
    exact zero_ne_one hsumOne

end Erdos85

#print axioms Erdos85.sum_poleOwnerSourceAt_eq_one
#print axioms Erdos85.poleOwner_cellwise_cancel_iff
#print axioms Erdos85.poleOwner_downstream_odd_of_cellwise_cancel
