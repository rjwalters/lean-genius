import Proofs.Erdos85SizeTwoEigenlineCyclicBaseResolvedReciprocity

/-!
# Target-column partition of the base-resolved tensor

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

The base partition laws do not yet remember that every local routing map is
a permutation of the admissible target columns.  In tensor coordinates the
target column of `(y,u)` is `y+u`.  This file proves that every admissible
absolute column contains exactly one tensor entry, while the two moving
columns contain none.
-/

namespace Erdos85

noncomputable section

/-- Tensor routes from `(x,t)` whose target cell has absolute column `z`. -/
def SizeTwoCyclicBaseResolvedColumnRoute
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) (z : ZMod q) :=
  Σ y : ZMod q, Σ u : sizeTwoAllowedDifference q a,
    {p : SizeTwoCyclicBaseResolvedRoute code x t y u // y + u.1 = z}

instance SizeTwoCyclicBaseResolvedColumnRoute.instFinite
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) (z : ZMod q) :
    Finite (SizeTwoCyclicBaseResolvedColumnRoute code x t z) := by
  unfold SizeTwoCyclicBaseResolvedColumnRoute
  infer_instance

noncomputable instance SizeTwoCyclicBaseResolvedColumnRoute.instFintype
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) (z : ZMod q) :
    Fintype (SizeTwoCyclicBaseResolvedColumnRoute code x t z) :=
  Fintype.ofFinite _

/-- Column-indexed tensor routes are equivalent to local rows whose
permutation column lands at `z`. -/
def sizeTwoCyclicBaseResolvedColumnRouteEquiv
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) (z : ZMod q) :
    SizeTwoCyclicBaseResolvedColumnRoute code x t z ≃
      {r : SizeTwoAdmissibleTargetRow q t.1 //
        x + (code.toPermutationCode.perm x t r).1 = z} where
  toFun p := by
    rcases p with ⟨y, u, ⟨r, hy, hu⟩, hz⟩
    subst u
    rw [← hy] at hz
    refine ⟨r, ?_⟩
    rw [← code.target_column_eq x t r]
    calc
      x + (r.1 + (code.targetDifference x t r).1) =
          (x + r.1) + (code.targetDifference x t r).1 := by abel
      _ = z := hz
  invFun r := by
    let u := code.targetDifference x t r.1
    let y := x + r.1.1
    refine ⟨y, u, ⟨⟨r.1, rfl, rfl⟩, ?_⟩⟩
    dsimp [y, u]
    calc
      x + r.1.1 + (code.targetDifference x t r.1).1 =
          x + (r.1.1 + (code.targetDifference x t r.1).1) := by abel
      _ = x + (code.toPermutationCode.perm x t r.1).1 := by
        rw [code.target_column_eq x t r.1]
      _ = z := r.2
  left_inv p := by
    rcases p with ⟨y, u, ⟨r, hy, hu⟩, hz⟩
    subst y
    subst u
    rfl
  right_inv r := by rfl

/-- Exact target-column partition law for the tensor. -/
theorem sizeTwoCyclicBaseResolvedColumnRoute_card
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a) (z : ZMod q) :
    Fintype.card (SizeTwoCyclicBaseResolvedColumnRoute code x t z) =
      if z - x ≠ 0 ∧ z - x ≠ (-1 : ZMod q) then 1 else 0 := by
  classical
  rw [Fintype.card_congr
    (sizeTwoCyclicBaseResolvedColumnRouteEquiv code x t z)]
  let Rows := {r : SizeTwoAdmissibleTargetRow q t.1 //
    x + (code.toPermutationCode.perm x t r).1 = z}
  by_cases hz : z - x ≠ 0 ∧ z - x ≠ (-1 : ZMod q)
  · rw [if_pos hz]
    let c : SizeTwoAdmissibleTargetColumn q := ⟨z - x, hz⟩
    let r0 : Rows := ⟨(code.toPermutationCode.perm x t).symm c, by
      simp [c]⟩
    letI : Unique Rows := {
      default := r0
      uniq := by
        intro r
        apply Subtype.ext
        apply (code.toPermutationCode.perm x t).injective
        apply Subtype.ext
        calc
          (code.toPermutationCode.perm x t r.1).1 =
              -x + (x + (code.toPermutationCode.perm x t r.1).1) := by abel
          _ = -x + z := by rw [r.2]
          _ = z - x := by abel
          _ = (code.toPermutationCode.perm x t r0.1).1 := by
            simp [r0, c] }
    exact Fintype.card_unique
  · rw [if_neg hz]
    haveI : IsEmpty Rows := ⟨by
      intro r
      apply hz
      have hval : (code.toPermutationCode.perm x t r.1).1 = z - x := by
        calc
          _ = -x + (x + (code.toPermutationCode.perm x t r.1).1) := by abel
          _ = -x + z := by rw [r.2]
          _ = z - x := by abel
      simpa [← hval] using (code.toPermutationCode.perm x t r.1).2⟩
    exact Fintype.card_eq_zero

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicBaseResolvedColumnRoute_card
