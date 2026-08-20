import Proofs.Erdos85SizeTwoEigenlineCyclicCanonicalReflectionPermutation

/-!
# Shifted agreements in reflected coordinates

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3.

The canonical reflected permutations turn equality of absolute routing
columns into an affine agreement equation on row coordinates.  Consequently
the C4 packing constraint says that, for distinct bases, the equation

`rho_(x+d,t)(r-d) = rho_(x,t)(r) + d`

has at most one admissible solution.  This removes the source/target type
mismatch and is the natural interface for correlation and sign arguments.
-/

namespace Erdos85

noncomputable section

/-- Pointwise conversion between routing-column and reflected affine
agreement. -/
theorem SizeTwoCyclicReciprocalPermutationCode.reflectedPerm_shifted_eq_iff
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1)
    (hshift : t.1 ≠ r.1 - d ∧ t.1 ≠ (r.1 - d) - 1) :
    (code.reflectedPerm (x + d) t ⟨r.1 - d, hshift⟩).1 =
        (code.reflectedPerm x t r).1 + d ↔
      x + (code.toPermutationCode.perm x t r).1 =
        (x + d) +
          (code.toPermutationCode.perm (x + d) t
            ⟨r.1 - d, hshift⟩).1 := by
  rw [code.reflectedPerm_val, code.reflectedPerm_val]
  constructor <;> intro h <;> linear_combination h

/-- A shifted agreement written entirely in the reflected row coordinates. -/
structure SizeTwoReflectedShiftedAgreement
    (q : ℕ) [NeZero q] (a : ZMod q)
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) where
  row : SizeTwoAdmissibleTargetRow q t.1
  shifted_admissible :
    t.1 ≠ row.1 - d ∧ t.1 ≠ (row.1 - d) - 1
  reflected_eq :
    (code.reflectedPerm (x + d) t
      ⟨row.1 - d, shifted_admissible⟩).1 =
        (code.reflectedPerm x t row).1 + d

/-- Reflected affine agreements are exactly the original shifted routing
agreements. -/
def sizeTwoReflectedShiftedAgreementEquiv
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) :
    SizeTwoReflectedShiftedAgreement q a code x d t ≃
      SizeTwoShiftedPermutationAgreement
        q a code.toPermutationCode.perm x d t where
  toFun w := ⟨w.row, w.shifted_admissible,
    (code.reflectedPerm_shifted_eq_iff
      x d t w.row w.shifted_admissible).mp w.reflected_eq⟩
  invFun w := ⟨w.row, w.shifted_admissible,
    (code.reflectedPerm_shifted_eq_iff
      x d t w.row w.shifted_admissible).mpr w.column_eq⟩
  left_inv w := by cases w; rfl
  right_inv w := by cases w; rfl

instance SizeTwoReflectedShiftedAgreement.instFinite
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) :
    Finite (SizeTwoReflectedShiftedAgreement q a code x d t) :=
  Finite.of_injective
    (sizeTwoReflectedShiftedAgreementEquiv code x d t)
    (sizeTwoReflectedShiftedAgreementEquiv code x d t).injective

noncomputable instance SizeTwoReflectedShiftedAgreement.instFintype
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) :
    Fintype (SizeTwoReflectedShiftedAgreement q a code x d t) :=
  Fintype.ofFinite _

/-- The packing law in same-coordinate reflected form. -/
theorem sizeTwoReflectedShiftedAgreement_card_le_one
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (hd : d ≠ 0)
    (t : sizeTwoAllowedDifference q a) :
    Fintype.card (SizeTwoReflectedShiftedAgreement q a code x d t) ≤ 1 := by
  rw [Fintype.card_congr
    (sizeTwoReflectedShiftedAgreementEquiv code x d t)]
  exact code.toPermutationCode.agreement_le_one x d hd t

end

end Erdos85

#print axioms Erdos85.sizeTwoReflectedShiftedAgreement_card_le_one
