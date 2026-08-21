import Proofs.Erdos85SizeTwoEigenlineCyclicSharpRepairSign

/-!
# Completing a permutation across two moving holes

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3.

If a permutation moves two distinguished holes away from both old holes,
its restriction is only a partial permutation of the twice-punctured set.
There are two canonical completions, obtained by matching the two new holes
to the old holes in parallel or crosswise.  Both agree with the original
permutation wherever it stays inside the punctured set.  This isolates the
moving-hole bookkeeping needed to compare shifted cyclic routing words.
-/

namespace Erdos85

noncomputable section

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- The type obtained by deleting two points. -/
abbrev TwoHoleComplement (A : Type*) (h₀ h₁ : A) :=
  {x : A // x ≠ h₀ ∧ x ≠ h₁}

/-- Pair each image-hole with its corresponding old hole. -/
def twoHoleParallelRepair
    {A : Type*} [DecidableEq A]
    (tau : Equiv.Perm A) (h₀ h₁ : A) : Equiv.Perm A :=
  (tau.trans (Equiv.swap (tau h₀) h₀)).trans
    (Equiv.swap (tau h₁) h₁)

/-- Cross the two pairings between image-holes and old holes. -/
def twoHoleCrossRepair
    {A : Type*} [DecidableEq A]
    (tau : Equiv.Perm A) (h₀ h₁ : A) : Equiv.Perm A :=
  (tau.trans (Equiv.swap (tau h₀) h₁)).trans
    (Equiv.swap (tau h₁) h₀)

theorem twoHoleParallelRepair_hole_zero
    {A : Type*} [DecidableEq A]
    (tau : Equiv.Perm A) (h₀ h₁ : A)
    (hholes : h₀ ≠ h₁)
    (hcross : tau h₀ ≠ tau h₁)
    (h₀₀ : tau h₀ ≠ h₀) (h₀₁ : tau h₀ ≠ h₁)
    (h₁₀ : tau h₁ ≠ h₀) (h₁₁ : tau h₁ ≠ h₁) :
    twoHoleParallelRepair tau h₀ h₁ h₀ = h₀ := by
  simp [twoHoleParallelRepair, Equiv.swap_apply_def, hholes, hholes.symm,
    hcross, hcross.symm, h₀₀, h₀₀.symm, h₀₁, h₀₁.symm,
    h₁₀, h₁₀.symm, h₁₁, h₁₁.symm]

theorem twoHoleParallelRepair_hole_one
    {A : Type*} [DecidableEq A]
    (tau : Equiv.Perm A) (h₀ h₁ : A)
    (hholes : h₀ ≠ h₁)
    (hcross : tau h₀ ≠ tau h₁)
    (h₀₀ : tau h₀ ≠ h₀) (h₀₁ : tau h₀ ≠ h₁)
    (h₁₀ : tau h₁ ≠ h₀) (h₁₁ : tau h₁ ≠ h₁) :
    twoHoleParallelRepair tau h₀ h₁ h₁ = h₁ := by
  simp [twoHoleParallelRepair, Equiv.swap_apply_def, hholes, hholes.symm,
    hcross, hcross.symm, h₀₀, h₀₀.symm, h₀₁, h₀₁.symm,
    h₁₀, h₁₀.symm, h₁₁, h₁₁.symm]

theorem twoHoleCrossRepair_hole_zero
    {A : Type*} [DecidableEq A]
    (tau : Equiv.Perm A) (h₀ h₁ : A)
    (hholes : h₀ ≠ h₁)
    (hcross : tau h₀ ≠ tau h₁)
    (h₀₀ : tau h₀ ≠ h₀) (h₀₁ : tau h₀ ≠ h₁)
    (h₁₀ : tau h₁ ≠ h₀) (h₁₁ : tau h₁ ≠ h₁) :
    twoHoleCrossRepair tau h₀ h₁ h₀ = h₁ := by
  simp [twoHoleCrossRepair, Equiv.swap_apply_def, hholes, hholes.symm,
    hcross, hcross.symm, h₀₀, h₀₀.symm, h₀₁, h₀₁.symm,
    h₁₀, h₁₀.symm, h₁₁, h₁₁.symm]

theorem twoHoleCrossRepair_hole_one
    {A : Type*} [DecidableEq A]
    (tau : Equiv.Perm A) (h₀ h₁ : A)
    (hholes : h₀ ≠ h₁)
    (hcross : tau h₀ ≠ tau h₁)
    (h₀₀ : tau h₀ ≠ h₀) (h₀₁ : tau h₀ ≠ h₁)
    (h₁₀ : tau h₁ ≠ h₀) (h₁₁ : tau h₁ ≠ h₁) :
    twoHoleCrossRepair tau h₀ h₁ h₁ = h₀ := by
  simp [twoHoleCrossRepair, Equiv.swap_apply_def, hholes, hholes.symm,
    hcross, hcross.symm, h₀₀, h₀₀.symm, h₀₁, h₀₁.symm,
    h₁₀, h₁₀.symm, h₁₁, h₁₁.symm]

/-- The parallel repair restricts to the twice-punctured complement. -/
def twoHoleParallelCompletion
    {A : Type*} [DecidableEq A]
    (tau : Equiv.Perm A) (h₀ h₁ : A)
    (hholes : h₀ ≠ h₁)
    (hcross : tau h₀ ≠ tau h₁)
    (h₀₀ : tau h₀ ≠ h₀) (h₀₁ : tau h₀ ≠ h₁)
    (h₁₀ : tau h₁ ≠ h₀) (h₁₁ : tau h₁ ≠ h₁) :
    Equiv.Perm (TwoHoleComplement A h₀ h₁) :=
  Equiv.subtypeEquiv (twoHoleParallelRepair tau h₀ h₁) (by
    intro r
    constructor
    · intro hr
      constructor
      · intro heq
        apply hr.1
        apply (twoHoleParallelRepair tau h₀ h₁).injective
        rw [heq, twoHoleParallelRepair_hole_zero tau h₀ h₁
          hholes hcross h₀₀ h₀₁ h₁₀ h₁₁]
      · intro heq
        apply hr.2
        apply (twoHoleParallelRepair tau h₀ h₁).injective
        rw [heq, twoHoleParallelRepair_hole_one tau h₀ h₁
          hholes hcross h₀₀ h₀₁ h₁₀ h₁₁]
    · intro hr
      constructor
      · intro heq
        subst r
        exact hr.1 (twoHoleParallelRepair_hole_zero tau h₀ h₁
          hholes hcross h₀₀ h₀₁ h₁₀ h₁₁)
      · intro heq
        subst r
        exact hr.2 (twoHoleParallelRepair_hole_one tau h₀ h₁
          hholes hcross h₀₀ h₀₁ h₁₀ h₁₁))

/-- The crossed repair also restricts to the twice-punctured complement. -/
def twoHoleCrossCompletion
    {A : Type*} [DecidableEq A]
    (tau : Equiv.Perm A) (h₀ h₁ : A)
    (hholes : h₀ ≠ h₁)
    (hcross : tau h₀ ≠ tau h₁)
    (h₀₀ : tau h₀ ≠ h₀) (h₀₁ : tau h₀ ≠ h₁)
    (h₁₀ : tau h₁ ≠ h₀) (h₁₁ : tau h₁ ≠ h₁) :
    Equiv.Perm (TwoHoleComplement A h₀ h₁) :=
  Equiv.subtypeEquiv (twoHoleCrossRepair tau h₀ h₁) (by
    intro r
    constructor
    · intro hr
      constructor
      · intro heq
        apply hr.2
        apply (twoHoleCrossRepair tau h₀ h₁).injective
        rw [heq, twoHoleCrossRepair_hole_one tau h₀ h₁
          hholes hcross h₀₀ h₀₁ h₁₀ h₁₁]
      · intro heq
        apply hr.1
        apply (twoHoleCrossRepair tau h₀ h₁).injective
        rw [heq, twoHoleCrossRepair_hole_zero tau h₀ h₁
          hholes hcross h₀₀ h₀₁ h₁₀ h₁₁]
    · intro hr
      constructor
      · intro heq
        subst r
        exact hr.2 (twoHoleCrossRepair_hole_zero tau h₀ h₁
          hholes hcross h₀₀ h₀₁ h₁₀ h₁₁)
      · intro heq
        subst r
        exact hr.1 (twoHoleCrossRepair_hole_one tau h₀ h₁
          hholes hcross h₀₀ h₀₁ h₁₀ h₁₁))

/-- On every point whose image avoids the two holes, the parallel completion
is exactly the original permutation. -/
theorem twoHoleParallelCompletion_apply_of_image_avoids
    {A : Type*} [DecidableEq A]
    (tau : Equiv.Perm A) (h₀ h₁ : A)
    (hholes : h₀ ≠ h₁) (hcross : tau h₀ ≠ tau h₁)
    (h₀₀ : tau h₀ ≠ h₀) (h₀₁ : tau h₀ ≠ h₁)
    (h₁₀ : tau h₁ ≠ h₀) (h₁₁ : tau h₁ ≠ h₁)
    (r : TwoHoleComplement A h₀ h₁)
    (hr₀ : tau r.1 ≠ h₀) (hr₁ : tau r.1 ≠ h₁) :
    (twoHoleParallelCompletion tau h₀ h₁ hholes hcross
      h₀₀ h₀₁ h₁₀ h₁₁ r).1 = tau r.1 := by
  have hrm₀ : tau r.1 ≠ tau h₀ := fun h => r.2.1 (tau.injective h)
  have hrm₁ : tau r.1 ≠ tau h₁ := fun h => r.2.2 (tau.injective h)
  simp [twoHoleParallelCompletion, twoHoleParallelRepair,
    Equiv.swap_apply_def, hr₀, hr₀.symm, hr₁, hr₁.symm,
    hrm₀, hrm₀.symm, hrm₁, hrm₁.symm]

/-- The crossed completion has the same common-domain action. -/
theorem twoHoleCrossCompletion_apply_of_image_avoids
    {A : Type*} [DecidableEq A]
    (tau : Equiv.Perm A) (h₀ h₁ : A)
    (hholes : h₀ ≠ h₁) (hcross : tau h₀ ≠ tau h₁)
    (h₀₀ : tau h₀ ≠ h₀) (h₀₁ : tau h₀ ≠ h₁)
    (h₁₀ : tau h₁ ≠ h₀) (h₁₁ : tau h₁ ≠ h₁)
    (r : TwoHoleComplement A h₀ h₁)
    (hr₀ : tau r.1 ≠ h₀) (hr₁ : tau r.1 ≠ h₁) :
    (twoHoleCrossCompletion tau h₀ h₁ hholes hcross
      h₀₀ h₀₁ h₁₀ h₁₁ r).1 = tau r.1 := by
  have hrm₀ : tau r.1 ≠ tau h₀ := fun h => r.2.1 (tau.injective h)
  have hrm₁ : tau r.1 ≠ tau h₁ := fun h => r.2.2 (tau.injective h)
  simp [twoHoleCrossCompletion, twoHoleCrossRepair,
    Equiv.swap_apply_def, hr₀, hr₀.symm, hr₁, hr₁.symm,
    hrm₀, hrm₀.symm, hrm₁, hrm₁.symm]

/-- The two completions have opposite sign: their relative permutation is
the transposition of the two exceptional preimages. -/
theorem twoHoleCompletion_relative_sign
    {A : Type*} [Fintype A] [DecidableEq A]
    (tau : Equiv.Perm A) (h₀ h₁ : A)
    (hholes : h₀ ≠ h₁) (hcross : tau h₀ ≠ tau h₁)
    (h₀₀ : tau h₀ ≠ h₀) (h₀₁ : tau h₀ ≠ h₁)
    (h₁₀ : tau h₁ ≠ h₀) (h₁₁ : tau h₁ ≠ h₁) :
    Equiv.Perm.sign
      ((twoHoleCrossCompletion tau h₀ h₁ hholes hcross
          h₀₀ h₀₁ h₁₀ h₁₁).trans
        (twoHoleParallelCompletion tau h₀ h₁ hholes hcross
          h₀₀ h₀₁ h₁₀ h₁₁).symm) = -1 := by
  let b₀ : TwoHoleComplement A h₀ h₁ := ⟨tau.symm h₀, by
    constructor
    · intro h
      apply h₀₀
      simpa [h] using tau.apply_symm_apply h₀
    · intro h
      apply h₁₀
      simpa [h] using tau.apply_symm_apply h₀⟩
  let b₁ : TwoHoleComplement A h₀ h₁ := ⟨tau.symm h₁, by
    constructor
    · intro h
      apply h₀₁
      simpa [h] using tau.apply_symm_apply h₁
    · intro h
      apply h₁₁
      simpa [h] using tau.apply_symm_apply h₁⟩
  have hbne : b₀ ≠ b₁ := by
    intro h
    apply hholes
    have := congrArg (fun z => tau z.1) h
    simpa [b₀, b₁] using this
  apply relativeEquiv_sign_eq_neg_one_of_exchange
    (twoHoleParallelCompletion tau h₀ h₁ hholes hcross
      h₀₀ h₀₁ h₁₀ h₁₁)
    (twoHoleCrossCompletion tau h₀ h₁ hholes hcross
      h₀₀ h₀₁ h₁₀ h₁₁)
    b₀ b₁ hbne
  · apply Subtype.ext
    simp [b₀, b₁, twoHoleParallelCompletion, twoHoleCrossCompletion,
      twoHoleParallelRepair, twoHoleCrossRepair, Equiv.swap_apply_def,
      hholes, hholes.symm, hcross, hcross.symm,
      h₀₀, h₀₀.symm, h₀₁, h₀₁.symm,
      h₁₀, h₁₀.symm, h₁₁, h₁₁.symm]
  · apply Subtype.ext
    simp [b₀, b₁, twoHoleParallelCompletion, twoHoleCrossCompletion,
      twoHoleParallelRepair, twoHoleCrossRepair, Equiv.swap_apply_def,
      hholes, hholes.symm, hcross, hcross.symm,
      h₀₀, h₀₀.symm, h₀₁, h₀₁.symm,
      h₁₀, h₁₀.symm, h₁₁, h₁₁.symm]
  · intro r hr₀ hr₁
    apply Subtype.ext
    have him₀ : tau r.1 ≠ h₀ := by
      intro h
      apply hr₀
      apply Subtype.ext
      simpa [b₀] using congrArg tau.symm h
    have him₁ : tau r.1 ≠ h₁ := by
      intro h
      apply hr₁
      apply Subtype.ext
      simpa [b₁] using congrArg tau.symm h
    rw [twoHoleCrossCompletion_apply_of_image_avoids tau h₀ h₁
      hholes hcross h₀₀ h₀₁ h₁₀ h₁₁ r him₀ him₁,
      twoHoleParallelCompletion_apply_of_image_avoids tau h₀ h₁
      hholes hcross h₀₀ h₀₁ h₁₀ h₁₁ r him₀ him₁]

end

end Erdos85

#print axioms Erdos85.twoHoleParallelCompletion
#print axioms Erdos85.twoHoleCrossCompletion
#print axioms Erdos85.twoHoleCompletion_relative_sign
