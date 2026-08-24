import Proofs.Erdos85PairedStarTWordGaugeParity

/-!
# Witness-label character surviving every local switch

This file formalizes `(73rnz_cjibkzp)--(73rnz_cjibkzq)`.  Private flip
occurrences retain their witness label.  Every within-witness re-pairing
relation has even label incidence, so the residual-witness character is
unchanged by all local switches.  A nonzero `Delta` therefore cannot be
removed by further star-local pairing; a cross-witness owner relation is
logically necessary.
-/

namespace Erdos85

/-- Incidence of a private occurrence census at each witness label. -/
def witnessIncidence
    {E W : Type*} [Fintype E] [DecidableEq W]
    (witness : E → W) (z : E → ZMod 2) (y : W) : ZMod 2 :=
  ∑ e, if witness e = y then z e else 0

/-- The character detecting incidence on a chosen residual witness set. -/
def residualWitnessCharacter
    {E W : Type*} [Fintype E] [Fintype W]
    [DecidableEq W] (witness : E → W) (R : Finset W)
    (z : E → ZMod 2) : ZMod 2 :=
  ∑ y ∈ R, witnessIncidence witness z y

/-- Witness incidence is linear in the private occurrence census. -/
theorem witnessIncidence_add
    {E W : Type*} [Fintype E] [DecidableEq W]
    (witness : E → W) (z r : E → ZMod 2) (y : W) :
    witnessIncidence witness (z + r) y =
      witnessIncidence witness z y + witnessIncidence witness r y := by
  unfold witnessIncidence
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Pi.add_apply]
  split_ifs <;> ring

/-- Any relation with even incidence at every witness leaves the entire
witness-incidence vector unchanged. -/
theorem witnessIncidence_add_eq_of_localKernel
    {E W : Type*} [Fintype E] [DecidableEq W]
    (witness : E → W) (z r : E → ZMod 2)
    (hr : ∀ y, witnessIncidence witness r y = 0) :
    witnessIncidence witness (z + r) = witnessIncidence witness z := by
  funext y
  rw [witnessIncidence_add, hr, add_zero]

/-- Consequently the residual witness character descends through all local
four-switch relations. -/
theorem residualWitnessCharacter_add_eq_of_localKernel
    {E W : Type*} [Fintype E] [Fintype W]
    [DecidableEq W] (witness : E → W) (R : Finset W)
    (z r : E → ZMod 2)
    (hr : ∀ y, witnessIncidence witness r y = 0) :
    residualWitnessCharacter witness R (z + r) =
      residualWitnessCharacter witness R z := by
  unfold residualWitnessCharacter
  apply Finset.sum_congr rfl
  intro y _
  rw [witnessIncidence_add, hr, add_zero]

/-- A finite sum of local switch relations is still invisible to every
witness label. -/
theorem witnessIncidence_sum_localKernel
    {E W I : Type*} [Fintype E] [Fintype I]
    [DecidableEq W]
    (witness : E → W) (rel : I → E → ZMod 2)
    (hrel : ∀ i y, witnessIncidence witness (rel i) y = 0) (y : W) :
    witnessIncidence witness (fun e => ∑ i, rel i e) y = 0 := by
  unfold witnessIncidence
  have hdistrib : ∀ e : E,
      (if witness e = y then (∑ i, rel i e) else 0) =
        ∑ i, if witness e = y then rel i e else 0 := by
    intro e
    split_ifs <;> simp
  simp_rw [hdistrib]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i _
  exact hrel i y

/-- **Local no-go.** If the residual character is one, adding any combination
of within-witness switches cannot annihilate the realized census. -/
theorem ne_zero_of_residualWitnessCharacter_one_after_localSwitch
    {E W : Type*} [Fintype E] [Fintype W]
    [DecidableEq W] (witness : E → W) (R : Finset W)
    (z r : E → ZMod 2)
    (hz : residualWitnessCharacter witness R z = 1)
    (hr : ∀ y, witnessIncidence witness r y = 0) :
    z + r ≠ 0 := by
  intro hzero
  have hchar := residualWitnessCharacter_add_eq_of_localKernel
    witness R z r hr
  rw [hzero] at hchar
  have hzeroChar : residualWitnessCharacter witness R (0 : E → ZMod 2) = 0 := by
    unfold residualWitnessCharacter witnessIncidence
    simp
  rw [hzeroChar, hz] at hchar
  exact zero_ne_one hchar

end Erdos85

#print axioms Erdos85.witnessIncidence_add
#print axioms Erdos85.witnessIncidence_add_eq_of_localKernel
#print axioms Erdos85.residualWitnessCharacter_add_eq_of_localKernel
#print axioms Erdos85.witnessIncidence_sum_localKernel
#print axioms Erdos85.ne_zero_of_residualWitnessCharacter_one_after_localSwitch
