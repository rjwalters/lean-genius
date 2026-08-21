import Proofs.Erdos85SizeTwoEigenlineCyclicReflectedAgreement
import Proofs.Erdos85SizeTwoEigenlineCyclicMatchingCounts

/-!
# Base-resolved Hamming separation of reflected permutations

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3.

After translating the row coordinate by a nonzero base shift, two punctured
row domains overlap in at least `q-4` places.  The C4 packing law permits at
most one affine agreement there.  Hence the corresponding reflected local
permutations disagree on at least `q-5` common rows.  Unlike the aggregate
defect ledgers, this statement retains both the base and the shifted row.
-/

namespace Erdos85

noncomputable section

/-- Rows admissible both before and after translation by `d`. -/
def sizeTwoReflectedCommonRows
    (q : ℕ) [NeZero q] (t : ZMod q) (d : ZMod q) :
    Finset (SizeTwoAdmissibleTargetRow q t) := by
  classical
  exact Finset.univ.filter fun r =>
    t ≠ r.1 - d ∧ t ≠ (r.1 - d) - 1

/-- Translating a twice-punctured cyclic row domain loses at most two more
rows, so the common domain has at least `q-4` elements. -/
theorem sizeTwoReflectedCommonRows_card_ge_sub_four
    (q : ℕ) [NeZero q] (hq1 : (1 : ZMod q) ≠ 0)
    (t d : ZMod q) :
    q - 4 ≤ (sizeTwoReflectedCommonRows q t d).card := by
  classical
  let A := (Finset.univ : Finset (SizeTwoAdmissibleTargetRow q t))
  let bad := A.filter fun r =>
    ¬(t ≠ r.1 - d ∧ t ≠ (r.1 - d) - 1)
  have hbadImage : bad.image (fun r => r.1) ⊆ {t + d, t + d + 1} := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨r, hrbad, rfl⟩ := hz
    have hr := (Finset.mem_filter.mp hrbad).2
    simp only [not_and_or, not_ne_iff] at hr
    rw [Finset.mem_insert, Finset.mem_singleton]
    rcases hr with hr | hr
    · left
      symm
      calc
        t + d = (r.1 - d) + d := by rw [← hr]
        _ = r.1 := sub_add_cancel _ _
    · right
      calc
        r.1 = (r.1 - d - 1) + d + 1 := by abel
        _ = t + d + 1 := by rw [← hr]
  have hbad : bad.card ≤ 2 := by
    calc
      bad.card = (bad.image (fun r => r.1)).card := by
        rw [Finset.card_image_iff.mpr]
        intro r _ s _ hrs
        exact Subtype.ext hrs
      _ ≤ ({t + d, t + d + 1} : Finset (ZMod q)).card :=
        Finset.card_le_card hbadImage
      _ ≤ ({t + d + 1} : Finset (ZMod q)).card + 1 :=
        Finset.card_insert_le _ _
      _ = 2 := by simp
  have hpartition :
      (sizeTwoReflectedCommonRows q t d).card + bad.card = A.card := by
    simpa only [sizeTwoReflectedCommonRows, A, bad] using
      (Finset.card_filter_add_card_filter_not (s := A)
        (fun r : SizeTwoAdmissibleTargetRow q t =>
          t ≠ r.1 - d ∧ t ≠ (r.1 - d) - 1))
  have hA : A.card = q - 2 := by
    simp [A, sizeTwoAdmissibleTargetRow_card q t hq1]
  omega

/-- A row in the common domain before and after translation by `d`. -/
def SizeTwoReflectedCommonRow
    (q : ℕ) [NeZero q] (t d : ZMod q) :=
  {r : SizeTwoAdmissibleTargetRow q t //
    t ≠ r.1 - d ∧ t ≠ (r.1 - d) - 1}

noncomputable instance SizeTwoReflectedCommonRow.instFintype
    (q : ℕ) [NeZero q] (t d : ZMod q) :
    Fintype (SizeTwoReflectedCommonRow q t d) :=
  Fintype.ofInjective (fun r => r.1.1) (by
    intro r s h
    exact Subtype.ext (Subtype.ext h))

theorem sizeTwoReflectedCommonRow_card
    (q : ℕ) [NeZero q] (t d : ZMod q) :
    Fintype.card (SizeTwoReflectedCommonRow q t d) =
      (sizeTwoReflectedCommonRows q t d).card := by
  classical
  simp only [SizeTwoReflectedCommonRow, sizeTwoReflectedCommonRows,
    Fintype.card_subtype]

/-- A common row on which the reflected affine agreement equation fails. -/
structure SizeTwoReflectedShiftedDisagreement
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) where
  row : SizeTwoAdmissibleTargetRow q t.1
  shifted_admissible : t.1 ≠ row.1 - d ∧ t.1 ≠ (row.1 - d) - 1
  reflected_ne :
    (code.reflectedPerm (x + d) t
      ⟨row.1 - d, shifted_admissible⟩).1 ≠
      (code.reflectedPerm x t row).1 + d

theorem SizeTwoReflectedShiftedDisagreement.row_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    {code : SizeTwoCyclicReciprocalPermutationCode q a}
    {x d : ZMod q} {t : sizeTwoAllowedDifference q a} :
    Function.Injective
      (fun w : SizeTwoReflectedShiftedDisagreement code x d t => w.row) := by
  intro u v h
  cases u
  cases v
  cases h
  rfl

noncomputable instance SizeTwoReflectedShiftedDisagreement.instFintype
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) :
    Fintype (SizeTwoReflectedShiftedDisagreement code x d t) :=
  Fintype.ofInjective (fun w => w.row.1) (by
    intro u v h
    cases u
    cases v
    cases Subtype.ext h
    rfl)

private theorem sizeTwoReflectedShiftedAgreement_row_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    {code : SizeTwoCyclicReciprocalPermutationCode q a}
    {x d : ZMod q} {t : sizeTwoAllowedDifference q a} :
    Function.Injective
      (fun w : SizeTwoReflectedShiftedAgreement q a code x d t => w.row) := by
  intro u v h
  cases u
  cases v
  cases h
  rfl

/-- Every common row is uniquely either an affine agreement or an affine
disagreement. -/
def sizeTwoReflectedAgreementDisagreementEquiv
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) :
    (SizeTwoReflectedShiftedAgreement q a code x d t ⊕
      SizeTwoReflectedShiftedDisagreement code x d t) ≃
        SizeTwoReflectedCommonRow q t.1 d :=
  Equiv.ofBijective
    (fun w => match w with
      | Sum.inl w => ⟨w.row, w.shifted_admissible⟩
      | Sum.inr w => ⟨w.row, w.shifted_admissible⟩)
    ⟨by
      intro p w hpw
      cases p with
      | inl p =>
          cases w with
          | inl w =>
              apply congrArg Sum.inl
              apply sizeTwoReflectedShiftedAgreement_row_injective
              exact congrArg Subtype.val hpw
          | inr w =>
              exfalso
              have hrow : p.row = w.row := congrArg Subtype.val hpw
              apply w.reflected_ne
              simpa only [hrow] using p.reflected_eq
      | inr p =>
          cases w with
          | inl w =>
              exfalso
              have hrow : p.row = w.row := congrArg Subtype.val hpw
              apply p.reflected_ne
              simpa only [hrow] using w.reflected_eq
          | inr w =>
              apply congrArg Sum.inr
              apply SizeTwoReflectedShiftedDisagreement.row_injective
              exact congrArg Subtype.val hpw,
    by
      intro r
      by_cases h :
          (code.reflectedPerm (x + d) t
            ⟨r.1.1 - d, r.2⟩).1 =
              (code.reflectedPerm x t r.1).1 + d
      · exact ⟨Sum.inl ⟨r.1, r.2, h⟩, rfl⟩
      · exact ⟨Sum.inr ⟨r.1, r.2, h⟩, rfl⟩⟩

/-- The reflected permutations at distinct bases have punctured Hamming
distance at least `q-5`. -/
theorem sizeTwoReflectedShiftedDisagreement_card_ge_sub_five
    {q : ℕ} [NeZero q] (hq1 : (1 : ZMod q) ≠ 0) {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (hd : d ≠ 0)
    (t : sizeTwoAllowedDifference q a) :
    q - 5 ≤ Fintype.card
      (SizeTwoReflectedShiftedDisagreement code x d t) := by
  have hcommon := sizeTwoReflectedCommonRows_card_ge_sub_four
    q hq1 t.1 d
  rw [← sizeTwoReflectedCommonRow_card] at hcommon
  have hsplit := Fintype.card_congr
    (sizeTwoReflectedAgreementDisagreementEquiv code x d t)
  rw [Fintype.card_sum] at hsplit
  have hagree := sizeTwoReflectedShiftedAgreement_card_le_one
    code x d hd t
  omega

/-- Total base-resolved punctured Hamming mass in one difference fibre. -/
def sizeTwoReflectedShiftedDisagreementMass
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (t : sizeTwoAllowedDifference q a) : ℕ :=
  ∑ x : ZMod q, ∑ d ∈ (Finset.univ.erase (0 : ZMod q)),
    Fintype.card (SizeTwoReflectedShiftedDisagreement code x d t)

/-- Summed over ordered distinct base pairs, one fibre contributes at least
`q(q-1)(q-5)` reflected disagreements.  This is the base-resolved
order-`q^3` pressure absent from the aggregate first-moment route. -/
theorem sizeTwoReflectedShiftedDisagreementMass_ge
    {q : ℕ} [NeZero q] (hq1 : (1 : ZMod q) ≠ 0) {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (t : sizeTwoAllowedDifference q a) :
    q * (q - 1) * (q - 5) ≤
      sizeTwoReflectedShiftedDisagreementMass code t := by
  classical
  unfold sizeTwoReflectedShiftedDisagreementMass
  calc
    q * (q - 1) * (q - 5) =
        ∑ _x : ZMod q,
          ∑ _d ∈ (Finset.univ.erase (0 : ZMod q)), (q - 5) := by
      simp [ZMod.card, Nat.mul_assoc]
    _ ≤ ∑ x : ZMod q,
        ∑ d ∈ (Finset.univ.erase (0 : ZMod q)),
          Fintype.card
            (SizeTwoReflectedShiftedDisagreement code x d t) := by
      gcongr with x hx d hd
      exact sizeTwoReflectedShiftedDisagreement_card_ge_sub_five
        hq1 code x d (Finset.mem_erase.mp hd).1 t

end

end Erdos85

#print axioms Erdos85.sizeTwoReflectedCommonRows_card_ge_sub_four
#print axioms
  Erdos85.sizeTwoReflectedShiftedDisagreement_card_ge_sub_five
#print axioms Erdos85.sizeTwoReflectedShiftedDisagreementMass_ge
