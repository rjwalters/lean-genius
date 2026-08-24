import Proofs.Erdos85SizeTwoEigenlineCyclicBaseResolvedColumnPartition

/-!
# Boundary-column permutations of the cyclic route tensor

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

At a fixed source base and an admissible absolute target column, every
source-difference fibre has one route and every target-difference fibre is
hit once.  Hence the fibre labels on that column form a permutation.  The
two outer columns of adjacent bases give the boundary permutations whose
relative monodromy carries the parity-missing-rank obstruction.
-/

namespace Erdos85

noncomputable section

/-- Target-difference fibre reached from `t` in the relative target column
`c`.  The local row is obtained by inverting the row-to-column
permutation. -/
def sizeTwoCyclicColumnTargetDifference
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (c : SizeTwoAdmissibleTargetColumn q)
    (t : sizeTwoAllowedDifference q a) :
    sizeTwoAllowedDifference q a :=
  code.targetDifference x t
    ((code.toPermutationCode.perm x t).symm c)

/-- At a fixed admissible column, distinct source fibres route to distinct
target fibres. -/
theorem sizeTwoCyclicColumnTargetDifference_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (c : SizeTwoAdmissibleTargetColumn q) :
    Function.Injective (sizeTwoCyclicColumnTargetDifference code x c) := by
  classical
  intro t s htarget
  let rt : SizeTwoAdmissibleTargetRow q t.1 :=
    (code.toPermutationCode.perm x t).symm c
  let rs : SizeTwoAdmissibleTargetRow q s.1 :=
    (code.toPermutationCode.perm x s).symm c
  let u : sizeTwoAllowedDifference q a :=
    sizeTwoCyclicColumnTargetDifference code x c t
  have hut : code.targetDifference x t rt = u := rfl
  have hus : code.targetDifference x s rs = u := by
    change sizeTwoCyclicColumnTargetDifference code x c s = u
    rw [← htarget]
  have hrt : rt.1 + u.1 = c.1 := by
    rw [← hut, code.target_column_eq]
    simp [rt]
  have hrs : rs.1 + u.1 = c.1 := by
    rw [← hus, code.target_column_eq]
    simp [rs]
  have hr : rt.1 = rs.1 := by
    linear_combination hrt - hrs
  let y : ZMod q := x + rt.1
  let Routes := Σ v : sizeTwoAllowedDifference q a,
    SizeTwoCyclicBaseResolvedRoute code x v y u
  let pt : Routes := ⟨t, ⟨rt, rfl, hut⟩⟩
  let ps : Routes := ⟨s, ⟨rs, by simp [y, hr], hus⟩⟩
  have hcard : Fintype.card Routes = 1 := by
    rw [show Fintype.card Routes =
        ∑ v : sizeTwoAllowedDifference q a,
          Fintype.card (SizeTwoCyclicBaseResolvedRoute code x v y u) from
      Fintype.card_sigma]
    rw [sizeTwoCyclicBaseResolvedRoute_card_sum_sourceDifferences]
    have hadm := code.reverse_admissible x t rt
    rw [if_pos]
    constructor
    · simpa [y, hut] using hadm.1
    · simpa [y, hut] using hadm.2
  have hpts : pt = ps :=
    (Fintype.card_le_one_iff.mp (by omega : Fintype.card Routes ≤ 1)) pt ps
  exact congrArg Sigma.fst hpts

/-- The fibre map on any admissible target column is a permutation. -/
def sizeTwoCyclicColumnTargetDifferenceEquiv
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (c : SizeTwoAdmissibleTargetColumn q) :
    sizeTwoAllowedDifference q a ≃ sizeTwoAllowedDifference q a :=
  Equiv.ofBijective (sizeTwoCyclicColumnTargetDifference code x c)
    ⟨sizeTwoCyclicColumnTargetDifference_injective code x c,
      Finite.injective_iff_surjective.mp
        (sizeTwoCyclicColumnTargetDifference_injective code x c)⟩

/-- Route reversal transports a column-fibre value to its inverse value on
the moving reverse column.  The reverse column is retained as a subtype,
so its admissibility is supplied by the reverse local permutation itself. -/
theorem sizeTwoCyclicColumnTargetDifference_reverse
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (c : SizeTwoAdmissibleTargetColumn q)
    (t : sizeTwoAllowedDifference q a) :
    let r : SizeTwoAdmissibleTargetRow q t.1 :=
      (code.toPermutationCode.perm x t).symm c
    let u := code.targetDifference x t r
    let reverseRow : SizeTwoAdmissibleTargetRow q u.1 :=
      ⟨-r.1, code.reverse_admissible x t r⟩
    let reverseColumn : SizeTwoAdmissibleTargetColumn q :=
      code.toPermutationCode.perm (x + r.1) u reverseRow
    sizeTwoCyclicColumnTargetDifference code (x + r.1)
      reverseColumn u = t := by
  dsimp only
  unfold sizeTwoCyclicColumnTargetDifference
  rw [Equiv.symm_apply_apply]
  exact code.reverse_targetDifference x t
    ((code.toPermutationCode.perm x t).symm c)

/-- Coordinate form of moving-column transport.  Reversal sends the route
to relative column `t-r`, hence to absolute column `x+t`, and sends its
target fibre back to `t`. -/
theorem sizeTwoCyclicColumnTargetDifference_reverse_coordinates
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (c : SizeTwoAdmissibleTargetColumn q)
    (t : sizeTwoAllowedDifference q a) :
    let r : SizeTwoAdmissibleTargetRow q t.1 :=
      (code.toPermutationCode.perm x t).symm c
    let u := code.targetDifference x t r
    let reverseRow : SizeTwoAdmissibleTargetRow q u.1 :=
      ⟨-r.1, code.reverse_admissible x t r⟩
    let reverseColumn : SizeTwoAdmissibleTargetColumn q :=
      code.toPermutationCode.perm (x + r.1) u reverseRow
    reverseColumn.1 = t.1 - r.1 ∧
      (x + r.1) + reverseColumn.1 = x + t.1 ∧
      sizeTwoCyclicColumnTargetDifference code (x + r.1)
        reverseColumn u = t := by
  dsimp only
  have hcolumn := code.reciprocity x t
    ((code.toPermutationCode.perm x t).symm c)
  refine ⟨hcolumn, ?_, ?_⟩
  · rw [hcolumn]
    abel
  · exact sizeTwoCyclicColumnTargetDifference_reverse code x c t

/-- Relative monodromy between the fibre permutations on two admissible
source-base/column slices.  For adjacent bases, choosing their two outer
absolute columns gives the boundary monodromy from the PMR audit. -/
def sizeTwoCyclicColumnMonodromy
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (c : SizeTwoAdmissibleTargetColumn q)
    (y : ZMod q) (d : SizeTwoAdmissibleTargetColumn q) :
    sizeTwoAllowedDifference q a ≃ sizeTwoAllowedDifference q a :=
  (sizeTwoCyclicColumnTargetDifferenceEquiv code x c).trans
    (sizeTwoCyclicColumnTargetDifferenceEquiv code y d).symm

/-- Reversing the two boundary slices inverts their monodromy. -/
theorem sizeTwoCyclicColumnMonodromy_symm
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (c : SizeTwoAdmissibleTargetColumn q)
    (y : ZMod q) (d : SizeTwoAdmissibleTargetColumn q) :
    (sizeTwoCyclicColumnMonodromy code x c y d).symm =
      sizeTwoCyclicColumnMonodromy code y d x c := by
  ext t
  simp [sizeTwoCyclicColumnMonodromy]

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicColumnTargetDifference_injective
#print axioms Erdos85.sizeTwoCyclicColumnTargetDifferenceEquiv
#print axioms Erdos85.sizeTwoCyclicColumnTargetDifference_reverse
#print axioms
  Erdos85.sizeTwoCyclicColumnTargetDifference_reverse_coordinates
#print axioms Erdos85.sizeTwoCyclicColumnMonodromy_symm
