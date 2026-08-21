import Proofs.Erdos85SizeTwoEigenlineCyclicReflectedHammingDistance
import Proofs.Erdos85SizeTwoEigenlineCyclicDisplacementMultiplicityMoment
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

/-- An exact `2,0,1` fibre profile canonically supplies the two duplicate
occurrences and hence a sharp near-permutation witness.  This is the bridge
from the cyclic multiplicity profile to the repair-sign invariant. -/
theorem exists_sharpNearPermutationWitness_of_fiberProfile
    {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (f : A → B) (duplicateValue missingValue : B)
    (hne : duplicateValue ≠ missingValue)
    (hprofile : ∀ b : B,
      ((Finset.univ : Finset A).filter fun r => f r = b).card =
        if b = duplicateValue then 2 else if b = missingValue then 0 else 1) :
    ∃ w : SharpNearPermutationWitness A B,
      w.f = f ∧ w.duplicateValue = duplicateValue ∧
        w.missingValue = missingValue := by
  classical
  have hfiber (b : B) : Nat.card {r : A // f r = b} =
      if b = duplicateValue then 2 else if b = missingValue then 0 else 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact hprofile b
  have hdup : Nat.card {r : A // f r = duplicateValue} = 2 := by
    simpa [hne] using hfiber duplicateValue
  obtain ⟨first, second, hfirstSecond, hall⟩ := Nat.card_eq_two_iff.mp hdup
  have hdup_cases (r : A) (hr : f r = duplicateValue) :
      r = first.1 ∨ r = second.1 := by
    have hz : (⟨r, hr⟩ : {z : A // f z = duplicateValue}) ∈
        ({first, second} : Set {z : A // f z = duplicateValue}) := by
      rw [hall]
      trivial
    rcases hz with hz | hz
    · exact Or.inl (congrArg Subtype.val hz)
    · exact Or.inr (congrArg Subtype.val hz)
  have hmissing : Nat.card {r : A // f r = missingValue} = 0 := by
    simpa [hne.symm] using hfiber missingValue
  have hother (b : B) (hbd : b ≠ duplicateValue)
      (hbm : b ≠ missingValue) :
      Nat.card {r : A // f r = b} = 1 := by
    simpa [hbd, hbm] using hfiber b
  refine ⟨{
    f := f
    duplicateValue := duplicateValue
    missingValue := missingValue
    first := first.1
    second := second.1
    first_ne_second := fun h => hfirstSecond (Subtype.ext h)
    first_maps := first.2
    second_maps := second.2
    missing_not_mem := ?_
    surjective_except_missing := ?_
    injective_away_first := ?_
    injective_away_second := ?_ }, rfl, rfl, rfl⟩
  · intro r hr
    have hnonempty : Nonempty {z : A // f z = missingValue} := ⟨⟨r, hr⟩⟩
    have hpos : 0 < Nat.card {z : A // f z = missingValue} :=
      Nat.card_pos_iff.mpr ⟨hnonempty, inferInstance⟩
    omega
  · intro b hbm
    by_cases hbd : b = duplicateValue
    · subst b
      exact ⟨first.1, first.2⟩
    · have hone := hother b hbd hbm
      obtain ⟨z⟩ := (Nat.card_eq_one_iff_unique.mp hone).2
      exact ⟨z.1, z.2⟩
  · intro r s hrf hsf hrs
    by_cases hrd : f r = duplicateValue
    · have hsd : f s = duplicateValue := hrs ▸ hrd
      rcases hdup_cases r hrd with (hr | hr) <;>
        rcases hdup_cases s hsd with (hs | hs)
      · exact (hrf hr).elim
      · exact (hrf hr).elim
      · exact (hsf hs).elim
      · exact hr.trans hs.symm
    · have hrm : f r ≠ missingValue := by
        intro h
        have hpos : 0 < Nat.card {z : A // f z = missingValue} :=
          Nat.card_pos_iff.mpr ⟨⟨⟨r, h⟩⟩, inferInstance⟩
        omega
      have hsub := (Nat.card_eq_one_iff_unique.mp (hother (f r) hrd hrm)).1
      exact Subtype.ext_iff.mp (hsub.elim ⟨r, rfl⟩ ⟨s, hrs.symm⟩)
  · intro r s hrs hss heq
    by_cases hrd : f r = duplicateValue
    · have hsd : f s = duplicateValue := heq ▸ hrd
      rcases hdup_cases r hrd with (hr | hr) <;>
        rcases hdup_cases s hsd with (hs | hs)
      · exact hr.trans hs.symm
      · exact (hss hs).elim
      · exact (hrs hr).elim
      · exact (hrs hr).elim
    · have hrm : f r ≠ missingValue := by
        intro h
        have hpos : 0 < Nat.card {z : A // f z = missingValue} :=
          Nat.card_pos_iff.mpr ⟨⟨⟨r, h⟩⟩, inferInstance⟩
        omega
      have hsub := (Nat.card_eq_one_iff_unique.mp (hother (f r) hrd hrm)).1
      exact Subtype.ext_iff.mp (hsub.elim ⟨r, rfl⟩ ⟨s, heq.symm⟩)

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

/-- Against any fixed bijection, switching between the two repairs negates
the relative sign.  Thus comparisons of two sharp words carry a forced
checkerboard of signs, independently of how their duplicate rows are
ordered. -/
theorem SharpNearPermutationWitness.repair_comparison_sign_toggle
    {A B : Type*} [Fintype A] [DecidableEq A]
    (w : SharpNearPermutationWitness A B) (e : A ≃ B) :
    Equiv.Perm.sign (e.trans w.repairSecondEquiv.symm) =
      -Equiv.Perm.sign (e.trans w.repairFirstEquiv.symm) := by
  let pFirst : Equiv.Perm A := e.trans w.repairFirstEquiv.symm
  let pToggle : Equiv.Perm A :=
    w.repairFirstEquiv.trans w.repairSecondEquiv.symm
  let pSecond : Equiv.Perm A := e.trans w.repairSecondEquiv.symm
  have hcompose : pToggle * pFirst = pSecond := by
    ext r
    simp [pFirst, pToggle, pSecond]
  have hsign := congrArg Equiv.Perm.sign hcompose
  rw [map_mul] at hsign
  have htoggle : Equiv.Perm.sign pToggle = -1 := by
    exact relativeEquiv_sign_eq_neg_one_of_exchange
      w.repairSecondEquiv w.repairFirstEquiv
      w.first w.second w.first_ne_second
      (by
        simp [SharpNearPermutationWitness.repairFirstEquiv,
          SharpNearPermutationWitness.repairSecondEquiv,
          SharpNearPermutationWitness.repairFirstFun,
          SharpNearPermutationWitness.repairSecondFun])
      (by
        have hne : w.second ≠ w.first := w.first_ne_second.symm
        simp [SharpNearPermutationWitness.repairFirstEquiv,
          SharpNearPermutationWitness.repairSecondEquiv,
          SharpNearPermutationWitness.repairFirstFun,
          SharpNearPermutationWitness.repairSecondFun,
          w.first_ne_second, hne, w.first_maps, w.second_maps])
      (by
        intro r hr₁ hr₂
        simp [SharpNearPermutationWitness.repairFirstEquiv,
          SharpNearPermutationWitness.repairSecondEquiv,
          SharpNearPermutationWitness.repairFirstFun,
          SharpNearPermutationWitness.repairSecondFun, hr₁, hr₂])
  rw [htoggle] at hsign
  simpa using hsign.symm

/-- Switching the repair on the left side of a relative comparison also
negates its sign. -/
theorem SharpNearPermutationWitness.repair_comparison_sign_toggle_left
    {A B : Type*} [Fintype A] [DecidableEq A]
    (w : SharpNearPermutationWitness A B) (e : A ≃ B) :
    Equiv.Perm.sign (w.repairSecondEquiv.trans e.symm) =
      -Equiv.Perm.sign (w.repairFirstEquiv.trans e.symm) := by
  let pFirst : Equiv.Perm A := w.repairFirstEquiv.trans e.symm
  let pToggle : Equiv.Perm A :=
    w.repairSecondEquiv.trans w.repairFirstEquiv.symm
  let pSecond : Equiv.Perm A := w.repairSecondEquiv.trans e.symm
  have hcompose : pFirst * pToggle = pSecond := by
    ext r
    simp [pFirst, pToggle, pSecond]
  have hsign := congrArg Equiv.Perm.sign hcompose
  rw [map_mul, w.repair_relative_sign] at hsign
  simpa using hsign.symm

/-- The four pairwise repair comparisons of two sharp words form a sign
checkerboard: toggling one repair negates the sign, while toggling both
preserves it. -/
theorem SharpNearPermutationWitness.repair_comparison_sign_checkerboard
    {A B : Type*} [Fintype A] [DecidableEq A]
    (w₁ w₂ : SharpNearPermutationWitness A B) :
    Equiv.Perm.sign
        (w₂.repairSecondEquiv.trans w₁.repairSecondEquiv.symm) =
      Equiv.Perm.sign
        (w₂.repairFirstEquiv.trans w₁.repairFirstEquiv.symm) := by
  rw [w₁.repair_comparison_sign_toggle w₂.repairSecondEquiv,
    w₂.repair_comparison_sign_toggle_left w₁.repairFirstEquiv]
  simp

/-- A single repaired-word comparison is not invariant under the arbitrary
ordering of the two duplicate occurrences: the two possible values are
provably distinct.  Consequently a global product of local comparison signs
cannot be a canonical invariant until an additional reciprocity-compatible
rule couples the repair choices. -/
theorem SharpNearPermutationWitness.repair_comparison_sign_ne
    {A B : Type*} [Fintype A] [DecidableEq A]
    (w : SharpNearPermutationWitness A B) (e : A ≃ B) :
    Equiv.Perm.sign (e.trans w.repairSecondEquiv.symm) ≠
      Equiv.Perm.sign (e.trans w.repairFirstEquiv.symm) := by
  intro heq
  have htoggle := w.repair_comparison_sign_toggle e
  rw [heq] at htoggle
  let s := Equiv.Perm.sign (e.trans w.repairFirstEquiv.symm)
  have hval : (s : ℤ) = -(s : ℤ) := by
    exact congrArg Units.val htoggle
  have hszero : (s : ℤ) = 0 := by omega
  exact s.ne_zero hszero

/-- Every sharp cyclic target-difference word admits two bijective repairs
whose relative sign is odd.  This specializes the abstract repair lemma to
the exact multiplicity notion used by the A.5.3 routing code. -/
theorem exists_sizeTwoCyclicTargetDifferenceSharpRepairSign
    {q : ℕ} [NeZero q] {a : ZMod q}
    [DecidableEq (sizeTwoAllowedDifference q a)]
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    [DecidableEq (SizeTwoAdmissibleTargetRow q t.1)]
    (duplicateValue missingValue : sizeTwoAllowedDifference q a)
    (hne : duplicateValue ≠ missingValue)
    (hprofile : ∀ u : sizeTwoAllowedDifference q a,
      sizeTwoCyclicTargetDifferenceMultiplicity code x t u =
        if u = duplicateValue then 2 else if u = missingValue then 0 else 1) :
    ∃ w : SharpNearPermutationWitness
        (SizeTwoAdmissibleTargetRow q t.1) (sizeTwoAllowedDifference q a),
      w.f = code.targetDifference x t ∧
      w.duplicateValue = duplicateValue ∧
      w.missingValue = missingValue ∧
      @Equiv.Perm.sign _ (Classical.decEq _) inferInstance
        ((@SharpNearPermutationWitness.repairSecondEquiv _ _
            (Classical.decEq _) w).trans
          (@SharpNearPermutationWitness.repairFirstEquiv _ _
            (Classical.decEq _) w).symm) = -1 := by
  classical
  obtain ⟨w, hwf, hwd, hwm⟩ :=
    exists_sharpNearPermutationWitness_of_fiberProfile
      (code.targetDifference x t) duplicateValue missingValue hne (by
        intro u
        rw [← hprofile u]
        unfold sizeTwoCyclicTargetDifferenceMultiplicity
        apply congrArg Finset.card
        ext r
        simp)
  refine ⟨w, hwf, hwd, hwm, ?_⟩
  exact @SharpNearPermutationWitness.repair_relative_sign _ _ inferInstance
    (Classical.decEq _) w

end

end Erdos85

#print axioms Erdos85.relativeEquiv_eq_swap_of_exchange
#print axioms Erdos85.relativeEquiv_sign_eq_neg_one_of_exchange
#print axioms Erdos85.exists_sharpNearPermutationWitness_of_fiberProfile
#print axioms Erdos85.SharpNearPermutationWitness.repair_relative_sign
#print axioms Erdos85.SharpNearPermutationWitness.repair_comparison_sign_toggle
#print axioms Erdos85.SharpNearPermutationWitness.repair_comparison_sign_toggle_left
#print axioms Erdos85.SharpNearPermutationWitness.repair_comparison_sign_checkerboard
#print axioms Erdos85.SharpNearPermutationWitness.repair_comparison_sign_ne
#print axioms Erdos85.exists_sizeTwoCyclicTargetDifferenceSharpRepairSign
