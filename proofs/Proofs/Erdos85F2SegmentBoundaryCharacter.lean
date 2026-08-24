import Proofs.Erdos85ConnectedF2EdgeSwitchSpan

/-!
# The cross-witness segment boundary character

Routed flip segments have two witness labels.  Their endpoint incidence is
the quotient coordinate left invariant by all within-witness re-pairings.
This file proves the exact F₂ handshake identity used in
`A_REG_BAER_INVOLUTION_COUPLING_AUDIT.md`, equations
(73rnz_cjibkzk) and (73rnz_cjibkzq).
-/

namespace Erdos85

noncomputable section

/-- The F₂ indicator of a finite witness set. -/
def f2FinsetIndicator {W : Type*} [DecidableEq W]
    (R : Finset W) (w : W) : ZMod 2 :=
  if w ∈ R then 1 else 0

/-- Endpoint-incidence vector of an F₂-weighted family of routed segments.
The maps `left,right : E → W` retain the two actual witness labels of every
segment occurrence. -/
def f2SegmentIncidence
    {E W : Type*} [Fintype E] [DecidableEq W]
    (left right : E → W) (z : E → ZMod 2) : W → ZMod 2 :=
  ∑ e, z e • f2EndpointSwitch (left e) (right e)

/-- A two-ended segment contributes to a witness set exactly through the
sum of its two endpoint indicators. -/
theorem sum_f2EndpointSwitch_over_finset
    {W : Type*} [DecidableEq W]
    (R : Finset W) (a b : W) :
    (∑ w ∈ R, f2EndpointSwitch a b w) =
      f2FinsetIndicator R a + f2FinsetIndicator R b := by
  simp [f2EndpointSwitch, f2FinsetIndicator, Finset.sum_add_distrib,
    Pi.single_apply]

/-- **Cross-witness boundary character.**  Pairing the endpoint-incidence
vector with a residual witness set `R` equals the sum, over routed segments,
of their two-ended crossing characters.  No internal pairing variables
remain. -/
theorem f2SegmentIncidence_residualCharacter
    {E W : Type*} [Fintype E] [Fintype W]
    [DecidableEq W]
    (R : Finset W) (left right : E → W) (z : E → ZMod 2) :
    (∑ w ∈ R, f2SegmentIncidence left right z w) =
      ∑ e, z e *
        (f2FinsetIndicator R (left e) +
          f2FinsetIndicator R (right e)) := by
  calc
    (∑ w ∈ R, f2SegmentIncidence left right z w) =
        ∑ w ∈ R, ∑ e,
          z e * f2EndpointSwitch (left e) (right e) w := by
      simp [f2SegmentIncidence, Finset.sum_apply, smul_eq_mul]
    _ = ∑ e, ∑ w ∈ R,
          z e * f2EndpointSwitch (left e) (right e) w := by
      rw [Finset.sum_comm]
    _ = ∑ e, z e *
          (∑ w ∈ R, f2EndpointSwitch (left e) (right e) w) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.mul_sum]
    _ = ∑ e, z e *
        (f2FinsetIndicator R (left e) +
          f2FinsetIndicator R (right e)) := by
      apply Finset.sum_congr rfl
      intro e _
      rw [sum_f2EndpointSwitch_over_finset]

/-- The unweighted form used for an actual routed segment census. -/
theorem f2SegmentIncidence_one_residualCharacter
    {E W : Type*} [Fintype E] [Fintype W]
    [DecidableEq W]
    (R : Finset W) (left right : E → W) :
    (∑ w ∈ R, f2SegmentIncidence left right (fun _ => 1) w) =
      ∑ e, (f2FinsetIndicator R (left e) +
        f2FinsetIndicator R (right e)) := by
  simpa using f2SegmentIncidence_residualCharacter
    R left right (fun _ => 1)

/-- The two-ended character is one precisely when exactly one endpoint lies
in the residual witness set. -/
theorem f2EndpointResidualCharacter_eq_crossingIndicator
    {W : Type*} [DecidableEq W] (R : Finset W) (a b : W) :
    f2FinsetIndicator R a + f2FinsetIndicator R b =
      if (a ∈ R ∧ b ∉ R) ∨ (a ∉ R ∧ b ∈ R) then 1 else 0 := by
  by_cases ha : a ∈ R
  · by_cases hb : b ∈ R
    · simp only [f2FinsetIndicator, ha, hb, if_pos, not_true_eq_false,
        and_false, false_or]
      calc
        (1 : ZMod 2) + 1 = (2 : ZMod 2) * 1 := by ring
        _ = 0 := by
          have htwo : (2 : ZMod 2) = 0 :=
            CharP.cast_eq_zero (ZMod 2) 2
          rw [htwo, zero_mul]
    · simp [f2FinsetIndicator, ha, hb]
  · by_cases hb : b ∈ R
    · simp [f2FinsetIndicator, ha, hb]
    · simp [f2FinsetIndicator, ha, hb]

/-- Cardinality form of the cross-witness handshake identity: the residual
character of the full segment census is exactly the parity of segments with
one residual and one non-residual witness label. -/
theorem f2SegmentIncidence_one_eq_crossingCard
    {E W : Type*} [Fintype E] [Fintype W]
    [DecidableEq E] [DecidableEq W]
    (R : Finset W) (left right : E → W) :
    (∑ w ∈ R, f2SegmentIncidence left right (fun _ => 1) w) =
      ((Finset.univ.filter fun e =>
        (left e ∈ R ∧ right e ∉ R) ∨
          (left e ∉ R ∧ right e ∈ R)).card : ZMod 2) := by
  rw [f2SegmentIncidence_one_residualCharacter]
  calc
    (∑ e, (f2FinsetIndicator R (left e) +
        f2FinsetIndicator R (right e))) =
        ∑ e, if (left e ∈ R ∧ right e ∉ R) ∨
          (left e ∉ R ∧ right e ∈ R) then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro e _
      exact f2EndpointResidualCharacter_eq_crossingIndicator
        R (left e) (right e)
    _ = ((Finset.univ.filter fun e =>
        (left e ∈ R ∧ right e ∉ R) ∨
          (left e ∉ R ∧ right e ∈ R)).card : ZMod 2) := by
      simp

/-- The residual crossing character as a linear functional on weighted
segment occurrences. -/
def f2SegmentResidualCharacter
    {E W : Type*} [Fintype E] [DecidableEq W]
    (R : Finset W) (left right : E → W) :
    (E → ZMod 2) →ₗ[ZMod 2] ZMod 2 where
  toFun z := ∑ e, z e *
    (f2FinsetIndicator R (left e) + f2FinsetIndicator R (right e))
  map_add' z z' := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a z := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum,
      RingHom.id_apply]

/-- The residual character factors through the endpoint-incidence vector. -/
theorem f2SegmentResidualCharacter_eq_sum_incidence
    {E W : Type*} [Fintype E] [Fintype W]
    [DecidableEq W]
    (R : Finset W) (left right : E → W) (z : E → ZMod 2) :
    f2SegmentResidualCharacter R left right z =
      ∑ w ∈ R, f2SegmentIncidence left right z w := by
  exact (f2SegmentIncidence_residualCharacter R left right z).symm

/-- Consequently every relation with zero witness-endpoint incidence lies
in the kernel of the residual character.  This is the precise statement
that the character descends to the cross-witness quotient. -/
theorem f2SegmentResidualCharacter_eq_zero_of_incidence_eq_zero
    {E W : Type*} [Fintype E] [Fintype W]
    [DecidableEq W]
    (R : Finset W) (left right : E → W) (z : E → ZMod 2)
    (hz : f2SegmentIncidence left right z = 0) :
    f2SegmentResidualCharacter R left right z = 0 := by
  rw [f2SegmentResidualCharacter_eq_sum_incidence, hz]
  simp

end

end Erdos85

#print axioms Erdos85.sum_f2EndpointSwitch_over_finset
#print axioms Erdos85.f2SegmentIncidence_residualCharacter
#print axioms Erdos85.f2SegmentIncidence_one_residualCharacter
#print axioms Erdos85.f2SegmentIncidence_one_eq_crossingCard
#print axioms Erdos85.f2SegmentResidualCharacter_eq_sum_incidence
#print axioms Erdos85.f2SegmentResidualCharacter_eq_zero_of_incidence_eq_zero
