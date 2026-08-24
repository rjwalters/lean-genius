import Proofs.Erdos85F2WitnessFiberQuotient
import Proofs.Erdos85F2SegmentBoundaryCharacter

/-!
# Factorization from occurrence fibers to routed witness segments

This file joins the two exact Baer quotient layers.  A routed segment has
two occurrence endpoints, and each occurrence has a witness label.  Taking
endpoint incidence and then aggregating by witness is the same as first
labelling the two segment endpoints and then taking witness incidence.
-/

namespace Erdos85

noncomputable section

/-- Witness aggregation carries an occurrence endpoint switch to the
endpoint switch on its two witness labels. -/
theorem f2WitnessFiberSum_endpointSwitch
    {O Y : Type*} [Fintype O] [DecidableEq O] [DecidableEq Y]
    (label : O → Y) (a b : O) :
    f2WitnessFiberSum label (f2EndpointSwitch a b) =
      f2EndpointSwitch (label a) (label b) := by
  ext y
  have hsingle (c : O) :
      (∑ x with label x = y,
        (Pi.single c (1 : ZMod 2) : O → ZMod 2) x) =
        (Pi.single (label c) (1 : ZMod 2) : Y → ZMod 2) y := by
    by_cases hcy : label c = y
    · subst y
      calc
        (∑ x with label x = label c,
            (Pi.single c (1 : ZMod 2) : O → ZMod 2) x) =
            (Pi.single c (1 : ZMod 2) : O → ZMod 2) c := by
          apply Finset.sum_eq_single c
          · intro x hx hxc
            change (Pi.single c (1 : ZMod 2) : O → ZMod 2) x = 0
            simp [hxc]
          · intro hc
            exact (hc (Finset.mem_filter.mpr
              ⟨Finset.mem_univ c, rfl⟩)).elim
        _ = 1 := by simp
        _ = (Pi.single (label c) (1 : ZMod 2) : Y → ZMod 2) (label c) := by
          simp
    · calc
        (∑ x with label x = y,
            (Pi.single c (1 : ZMod 2) : O → ZMod 2) x) = 0 := by
          apply Finset.sum_eq_zero
          intro x hx
          apply Pi.single_eq_of_ne
          intro hxc
          subst x
          exact hcy (Finset.mem_filter.mp hx).2
        _ = (Pi.single (label c) (1 : ZMod 2) : Y → ZMod 2) y := by
          symm
          rw [Pi.single_eq_of_ne (fun h => hcy h.symm)]
  change (∑ x with label x = y, f2EndpointSwitch a b x) =
    f2EndpointSwitch (label a) (label b) y
  simp only [f2EndpointSwitch, Pi.add_apply]
  rw [Finset.sum_add_distrib, hsingle a, hsingle b]

/-- **Occurrence-to-witness naturality.**  Endpoint incidence followed by
fiber aggregation equals segment incidence of the labelled endpoints. -/
theorem f2WitnessFiberSum_segmentIncidence
    {E O Y : Type*} [Fintype E] [Fintype O]
    [DecidableEq O] [DecidableEq Y]
    (label : O → Y) (left right : E → O) (z : E → ZMod 2) :
    f2WitnessFiberSum label (f2SegmentIncidence left right z) =
      f2SegmentIncidence (label ∘ left) (label ∘ right) z := by
  rw [show f2SegmentIncidence left right z =
      ∑ e, z e • f2EndpointSwitch (left e) (right e) by rfl]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_smul, f2WitnessFiberSum_endpointSwitch]
  rfl

/-- The residual segment character therefore factors all the way through
the occurrence-fiber aggregation map. -/
theorem f2SegmentResidualCharacter_eq_sum_fiberAggregation
    {E O Y : Type*} [Fintype E] [Fintype O] [Fintype Y]
    [DecidableEq O] [DecidableEq Y]
    (R : Finset Y) (label : O → Y)
    (left right : E → O) (z : E → ZMod 2) :
    f2SegmentResidualCharacter R (label ∘ left) (label ∘ right) z =
      ∑ y ∈ R,
        f2WitnessFiberSum label (f2SegmentIncidence left right z) y := by
  rw [f2SegmentResidualCharacter_eq_sum_incidence,
    ← f2WitnessFiberSum_segmentIncidence]

/-- A two-pole witness source outside the residual set has zero residual
character.  This is the direct terminal once owner routes supply their
endpoint-incidence identity. -/
theorem f2SegmentResidualCharacter_eq_zero_of_incidence_eq_poleSwitch
    {E Y : Type*} [Fintype E] [Fintype Y]
    [DecidableEq Y]
    (R : Finset Y) (left right : E → Y) (z : E → ZMod 2)
    (pole₁ pole₂ : Y) (hpole₁ : pole₁ ∉ R) (hpole₂ : pole₂ ∉ R)
    (hsource : f2SegmentIncidence left right z =
      f2EndpointSwitch pole₁ pole₂) :
    f2SegmentResidualCharacter R left right z = 0 := by
  rw [f2SegmentResidualCharacter_eq_sum_incidence, hsource,
    sum_f2EndpointSwitch_over_finset]
  simp [f2FinsetIndicator, hpole₁, hpole₂]

/-- Full occurrence-level two-pole terminal.  It is enough to prove that
the witness aggregation of the routed occurrence incidence is the switch
of two poles outside `R`; the residual character then vanishes. -/
theorem f2SegmentResidualCharacter_eq_zero_of_fiberAggregation_eq_poleSwitch
    {E O Y : Type*} [Fintype E] [Fintype O] [Fintype Y]
    [DecidableEq O] [DecidableEq Y]
    (R : Finset Y) (label : O → Y)
    (left right : E → O) (z : E → ZMod 2)
    (pole₁ pole₂ : Y) (hpole₁ : pole₁ ∉ R) (hpole₂ : pole₂ ∉ R)
    (hsource : f2WitnessFiberSum label
      (f2SegmentIncidence left right z) =
        f2EndpointSwitch pole₁ pole₂) :
    f2SegmentResidualCharacter R (label ∘ left) (label ∘ right) z = 0 := by
  rw [f2SegmentResidualCharacter_eq_sum_fiberAggregation, hsource,
    sum_f2EndpointSwitch_over_finset]
  simp [f2FinsetIndicator, hpole₁, hpole₂]

end

end Erdos85

#print axioms Erdos85.f2WitnessFiberSum_endpointSwitch
#print axioms Erdos85.f2WitnessFiberSum_segmentIncidence
#print axioms Erdos85.f2SegmentResidualCharacter_eq_sum_fiberAggregation
#print axioms Erdos85.f2SegmentResidualCharacter_eq_zero_of_incidence_eq_poleSwitch
#print axioms Erdos85.f2SegmentResidualCharacter_eq_zero_of_fiberAggregation_eq_poleSwitch
