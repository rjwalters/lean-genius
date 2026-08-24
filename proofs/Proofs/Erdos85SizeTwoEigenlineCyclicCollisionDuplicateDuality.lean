import Proofs.Erdos85SizeTwoEigenlineCyclicBaseResolvedCommonTarget

/-!
# Collision--duplicate duality under route reversal

Node: `SIZE-TWO-EIGENLINE(q)`, beneath `GAP A-REG-NONBIP`.

A same-fiber common target for sources `(x,t)` and `(x+d,t)` reverses to two
routes in one target routing block, both returning to difference fiber `t`
and with endpoint bases separated by `d`.  This file records the exact
pointwise equivalence.  It is the interface needed to translate a
separation-resolved agreement cap into restrictions on local duplicate
target-difference labels.
-/

namespace Erdos85

noncomputable section

/-- A routing block `(y,u)` containing two routes into the same target
difference `t`, at target bases `x` and `x+d`. -/
def SizeTwoCyclicBaseResolvedDuplicateTarget
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) :=
  Σ y : ZMod q, Σ u : sizeTwoAllowedDifference q a,
    (SizeTwoCyclicBaseResolvedRoute code y u x t ×
      SizeTwoCyclicBaseResolvedRoute code y u (x + d) t)

noncomputable instance SizeTwoCyclicBaseResolvedCommonTarget.instFintype
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) :
    Fintype (SizeTwoCyclicBaseResolvedCommonTarget code x d t) := by
  unfold SizeTwoCyclicBaseResolvedCommonTarget
  infer_instance

noncomputable instance SizeTwoCyclicBaseResolvedDuplicateTarget.instFintype
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) :
    Fintype (SizeTwoCyclicBaseResolvedDuplicateTarget code x d t) := by
  unfold SizeTwoCyclicBaseResolvedDuplicateTarget
  infer_instance

/-- Reverse both incident routes: common targets and local duplicate target
labels are the same pointwise data. -/
def sizeTwoCyclicBaseResolvedCommonTargetEquivDuplicateTarget
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) :
    SizeTwoCyclicBaseResolvedCommonTarget code x d t ≃
      SizeTwoCyclicBaseResolvedDuplicateTarget code x d t where
  toFun p := by
    rcases p with ⟨y, u, left, right⟩
    exact ⟨y, u,
      sizeTwoCyclicBaseResolvedRouteReverse code x t y u left,
      sizeTwoCyclicBaseResolvedRouteReverse code (x + d) t y u right⟩
  invFun p := by
    rcases p with ⟨y, u, left, right⟩
    exact ⟨y, u,
      sizeTwoCyclicBaseResolvedRouteReverse code y u x t left,
      sizeTwoCyclicBaseResolvedRouteReverse code y u (x + d) t right⟩
  left_inv p := by
    rcases p with ⟨y, u, left, right⟩
    have hl : sizeTwoCyclicBaseResolvedRouteReverse code y u x t
          (sizeTwoCyclicBaseResolvedRouteReverse code x t y u left) = left :=
      (Fintype.card_le_one_iff.mp
        (sizeTwoCyclicBaseResolvedRoute_card_le_one code x t y u)) _ _
    have hr : sizeTwoCyclicBaseResolvedRouteReverse code y u (x + d) t
          (sizeTwoCyclicBaseResolvedRouteReverse code (x + d) t y u right) = right :=
      (Fintype.card_le_one_iff.mp
        (sizeTwoCyclicBaseResolvedRoute_card_le_one code (x + d) t y u)) _ _
    change (⟨y, u, (_, _)⟩ :
      SizeTwoCyclicBaseResolvedCommonTarget code x d t) =
        ⟨y, u, (left, right)⟩
    rw [hl, hr]
  right_inv p := by
    rcases p with ⟨y, u, left, right⟩
    have hl : sizeTwoCyclicBaseResolvedRouteReverse code x t y u
          (sizeTwoCyclicBaseResolvedRouteReverse code y u x t left) = left :=
      (Fintype.card_le_one_iff.mp
        (sizeTwoCyclicBaseResolvedRoute_card_le_one code y u x t)) _ _
    have hr : sizeTwoCyclicBaseResolvedRouteReverse code (x + d) t y u
          (sizeTwoCyclicBaseResolvedRouteReverse code y u (x + d) t right) = right :=
      (Fintype.card_le_one_iff.mp
        (sizeTwoCyclicBaseResolvedRoute_card_le_one code y u (x + d) t)) _ _
    change (⟨y, u, (_, _)⟩ :
      SizeTwoCyclicBaseResolvedDuplicateTarget code x d t) =
        ⟨y, u, (left, right)⟩
    rw [hl, hr]

/-- Cardinality form of collision--duplicate duality. -/
theorem sizeTwoCyclicBaseResolvedCommonTarget_card_eq_duplicateTarget_card
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) :
    Fintype.card (SizeTwoCyclicBaseResolvedCommonTarget code x d t) =
      Fintype.card (SizeTwoCyclicBaseResolvedDuplicateTarget code x d t) :=
  Fintype.card_congr
    (sizeTwoCyclicBaseResolvedCommonTargetEquivDuplicateTarget code x d t)

/-- Agreement at `(t,d)` says equivalently that at most one routing block
contains the corresponding pair of reversed routes into `t`. -/
theorem sizeTwoCyclicBaseResolvedDuplicateTarget_card_le_one
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicSameDifferenceCode q a)
    (x d : ZMod q) (hd : d ≠ 0)
    (t : sizeTwoAllowedDifference q a) :
    Fintype.card (SizeTwoCyclicBaseResolvedDuplicateTarget
      code.toReciprocalCode x d t) ≤ 1 := by
  rw [← sizeTwoCyclicBaseResolvedCommonTarget_card_eq_duplicateTarget_card]
  calc
    Fintype.card (SizeTwoCyclicBaseResolvedCommonTarget
        code.toReciprocalCode x d t) ≤
      Fintype.card (SizeTwoSameDifferenceCommonRoute q a
        code.toReciprocalCode x d t) :=
      Fintype.card_le_of_injective
        (sizeTwoCyclicBaseResolvedCommonTarget_toCommonRoute
          code.toReciprocalCode x d t)
        (sizeTwoCyclicBaseResolvedCommonTarget_toCommonRoute_injective
          code.toReciprocalCode x d t)
    _ ≤ 1 := sizeTwoSameDifferenceCommonRoute_card_le_one
      q a code x d hd t

end

end Erdos85

#print axioms
  Erdos85.sizeTwoCyclicBaseResolvedCommonTarget_card_eq_duplicateTarget_card
#print axioms Erdos85.sizeTwoCyclicBaseResolvedDuplicateTarget_card_le_one
