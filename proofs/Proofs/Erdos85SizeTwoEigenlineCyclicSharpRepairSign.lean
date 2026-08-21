import Proofs.Erdos85SizeTwoEigenlineCyclicReflectedHammingDistance
import Mathlib.GroupTheory.Perm.Sign

/-!
# Relative sign of the two sharp near-permutation repairs

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3.

A sharp target-fibre word has one duplicated value and one missing value.
Repairing either duplicate occurrence gives a bijection.  The two repairs
agree away from those occurrences and exchange their two images, so their
relative permutation is a transposition and has sign `-1`.

This abstract lemma isolates the sign fact needed before constructing the
repairs for the cyclic target-difference words and transporting their choices
through reciprocity.
-/

namespace Erdos85

noncomputable section

/-- Two equivalences which exchange their values at exactly `r₁,r₂` differ
by the transposition of those domain points. -/
theorem relativeEquiv_eq_swap_of_exchange
    {A B : Type*} [Fintype A] [DecidableEq A]
    (e₁ e₂ : A ≃ B) (r₁ r₂ : A)
    (h₁ : e₂ r₁ = e₁ r₂) (h₂ : e₂ r₂ = e₁ r₁)
    (hother : ∀ r, r ≠ r₁ → r ≠ r₂ → e₂ r = e₁ r) :
    e₂.trans e₁.symm = Equiv.swap r₁ r₂ := by
  ext r
  apply e₁.injective
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  by_cases hr₁ : r = r₁
  · subst r
    rw [h₁]
    simp
  · by_cases hr₂ : r = r₂
    · subst r
      rw [h₂]
      simp
    · rw [hother r hr₁ hr₂]
      simp [Equiv.swap_apply_def, hr₁, hr₂]

/-- The two repairs of a sharp near-permutation have opposite relative
sign: their quotient is odd. -/
theorem relativeEquiv_sign_eq_neg_one_of_exchange
    {A B : Type*} [Fintype A] [DecidableEq A]
    (e₁ e₂ : A ≃ B) (r₁ r₂ : A) (hne : r₁ ≠ r₂)
    (h₁ : e₂ r₁ = e₁ r₂) (h₂ : e₂ r₂ = e₁ r₁)
    (hother : ∀ r, r ≠ r₁ → r ≠ r₂ → e₂ r = e₁ r) :
    Equiv.Perm.sign (e₂.trans e₁.symm) = -1 := by
  rw [relativeEquiv_eq_swap_of_exchange e₁ e₂ r₁ r₂ h₁ h₂ hother]
  exact Equiv.Perm.sign_swap hne

/-- Data witnessing a sharp near-permutation: two domain points carry the
duplicated value, one codomain value is missing, and deleting either
duplicate occurrence leaves an injective map onto the non-missing values. -/
structure SharpNearPermutationWitness (A B : Type*) where
  f : A → B
  duplicateValue : B
  missingValue : B
  first : A
  second : A
  first_ne_second : first ≠ second
  first_maps : f first = duplicateValue
  second_maps : f second = duplicateValue
  missing_not_mem : ∀ r, f r ≠ missingValue
  surjective_except_missing : ∀ b, b ≠ missingValue → ∃ r, f r = b
  injective_away_first : ∀ {r s}, r ≠ first → s ≠ first → f r = f s → r = s
  injective_away_second : ∀ {r s}, r ≠ second → s ≠ second → f r = f s → r = s

/-- Repair the first duplicate occurrence by sending it to the missing
value. -/
def SharpNearPermutationWitness.repairFirstFun
    {A B : Type*} [DecidableEq A]
    (w : SharpNearPermutationWitness A B) (r : A) : B :=
  if r = w.first then w.missingValue else w.f r

/-- Repair the second duplicate occurrence. -/
def SharpNearPermutationWitness.repairSecondFun
    {A B : Type*} [DecidableEq A]
    (w : SharpNearPermutationWitness A B) (r : A) : B :=
  if r = w.second then w.missingValue else w.f r

theorem SharpNearPermutationWitness.repairFirst_bijective
    {A B : Type*} [DecidableEq A]
    (w : SharpNearPermutationWitness A B) :
    Function.Bijective w.repairFirstFun := by
  constructor
  · intro r s h
    by_cases hr : r = w.first
    · subst r
      by_cases hs : s = w.first
      · exact hs.symm
      · exfalso
        apply w.missing_not_mem s
        simpa [SharpNearPermutationWitness.repairFirstFun, hs] using h.symm
    · by_cases hs : s = w.first
      · subst s
        exfalso
        apply w.missing_not_mem r
        simpa [SharpNearPermutationWitness.repairFirstFun, hr] using h
      · apply w.injective_away_first hr hs
        simpa [SharpNearPermutationWitness.repairFirstFun, hr, hs] using h
  · intro b
    by_cases hb : b = w.missingValue
    · exact ⟨w.first, by simp [SharpNearPermutationWitness.repairFirstFun, hb]⟩
    · obtain ⟨r, hr⟩ := w.surjective_except_missing b hb
      by_cases hrf : r = w.first
      · refine ⟨w.second, ?_⟩
        have hs : w.second ≠ w.first := w.first_ne_second.symm
        simp only [SharpNearPermutationWitness.repairFirstFun, if_neg hs]
        rw [w.second_maps, ← w.first_maps, ← hrf, hr]
      · exact ⟨r, by simpa [SharpNearPermutationWitness.repairFirstFun, hrf]
          using hr⟩

theorem SharpNearPermutationWitness.repairSecond_bijective
    {A B : Type*} [DecidableEq A]
    (w : SharpNearPermutationWitness A B) :
    Function.Bijective w.repairSecondFun := by
  constructor
  · intro r s h
    by_cases hr : r = w.second
    · subst r
      by_cases hs : s = w.second
      · exact hs.symm
      · exfalso
        apply w.missing_not_mem s
        simpa [SharpNearPermutationWitness.repairSecondFun, hs] using h.symm
    · by_cases hs : s = w.second
      · subst s
        exfalso
        apply w.missing_not_mem r
        simpa [SharpNearPermutationWitness.repairSecondFun, hr] using h
      · apply w.injective_away_second hr hs
        simpa [SharpNearPermutationWitness.repairSecondFun, hr, hs] using h
  · intro b
    by_cases hb : b = w.missingValue
    · exact ⟨w.second, by simp [SharpNearPermutationWitness.repairSecondFun, hb]⟩
    · obtain ⟨r, hr⟩ := w.surjective_except_missing b hb
      by_cases hrs : r = w.second
      · refine ⟨w.first, ?_⟩
        have hf : w.first ≠ w.second := w.first_ne_second
        simp only [SharpNearPermutationWitness.repairSecondFun, if_neg hf]
        rw [w.first_maps, ← w.second_maps, ← hrs, hr]
      · exact ⟨r, by simpa [SharpNearPermutationWitness.repairSecondFun, hrs]
          using hr⟩

/-- The two actual repaired bijections. -/
def SharpNearPermutationWitness.repairFirstEquiv
    {A B : Type*} [DecidableEq A]
    (w : SharpNearPermutationWitness A B) : A ≃ B :=
  Equiv.ofBijective w.repairFirstFun w.repairFirst_bijective

def SharpNearPermutationWitness.repairSecondEquiv
    {A B : Type*} [DecidableEq A]
    (w : SharpNearPermutationWitness A B) : A ≃ B :=
  Equiv.ofBijective w.repairSecondFun w.repairSecond_bijective

/-- The relative sign of the two canonical sharp repairs is `-1`. -/
theorem SharpNearPermutationWitness.repair_relative_sign
    {A B : Type*} [Fintype A] [DecidableEq A]
    (w : SharpNearPermutationWitness A B) :
    Equiv.Perm.sign (w.repairSecondEquiv.trans w.repairFirstEquiv.symm) = -1 := by
  apply relativeEquiv_sign_eq_neg_one_of_exchange
    w.repairFirstEquiv w.repairSecondEquiv
    w.first w.second w.first_ne_second
  · have hne : w.second ≠ w.first := w.first_ne_second.symm
    simp [SharpNearPermutationWitness.repairFirstEquiv,
      SharpNearPermutationWitness.repairSecondEquiv,
      SharpNearPermutationWitness.repairFirstFun,
      SharpNearPermutationWitness.repairSecondFun,
      w.first_ne_second, hne, w.first_maps, w.second_maps]
  · simp [SharpNearPermutationWitness.repairFirstEquiv,
      SharpNearPermutationWitness.repairSecondEquiv,
      SharpNearPermutationWitness.repairFirstFun,
      SharpNearPermutationWitness.repairSecondFun]
  · intro r hr₁ hr₂
    simp [SharpNearPermutationWitness.repairFirstEquiv,
      SharpNearPermutationWitness.repairSecondEquiv,
      SharpNearPermutationWitness.repairFirstFun,
      SharpNearPermutationWitness.repairSecondFun, hr₁, hr₂]

end

end Erdos85

#print axioms Erdos85.relativeEquiv_eq_swap_of_exchange
#print axioms Erdos85.relativeEquiv_sign_eq_neg_one_of_exchange
#print axioms Erdos85.SharpNearPermutationWitness.repair_relative_sign
