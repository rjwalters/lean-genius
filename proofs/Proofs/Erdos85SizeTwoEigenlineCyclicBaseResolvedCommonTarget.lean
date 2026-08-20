import Proofs.Erdos85SizeTwoEigenlineCyclicBaseResolvedReciprocity
import Proofs.Erdos85SizeTwoEigenlineCyclicSameDifferenceCommonRoute

/-!
# The same-fiber common-target cap on the base tensor

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

The base-resolved tensor is globally partitioned, but it must also retain the
packing condition: two distinct bases in one difference fiber share at most
one precise target cell.  This file states that condition directly as an
inner-product bound between two tensor rows.
-/

namespace Erdos85

noncomputable section

/-- Precise target cells simultaneously routed from `(x,t)` and
`(x+d,t)`. -/
def SizeTwoCyclicBaseResolvedCommonTarget
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) :=
  Σ y : ZMod q, Σ u : sizeTwoAllowedDifference q a,
    (SizeTwoCyclicBaseResolvedRoute code x t y u ×
      SizeTwoCyclicBaseResolvedRoute code (x + d) t y u)

/-- Forgetting the tensor coordinates produces the corresponding routed
common target. -/
def sizeTwoCyclicBaseResolvedCommonTarget_toCommonRoute
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) :
    SizeTwoCyclicBaseResolvedCommonTarget code x d t →
      SizeTwoSameDifferenceCommonRoute q a code x d t := by
  intro p
  rcases p with ⟨y, u, left, right⟩
  refine ⟨sizeTwoCyclicCellAt q a y u, ?_, ?_⟩
  · rw [sizeTwoCyclicCodeRouteRel_cellAt_iff q a code x t]
    refine ⟨left.1, ?_⟩
    rw [left.2.1, left.2.2]
  · rw [sizeTwoCyclicCodeRouteRel_cellAt_iff q a code (x + d) t]
    refine ⟨right.1, ?_⟩
    rw [right.2.1, right.2.2]

/-- The coordinate-forgetting map is injective because a precise target cell
determines its base and difference, and each base-resolved route is unique. -/
theorem sizeTwoCyclicBaseResolvedCommonTarget_toCommonRoute_injective
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (x d : ZMod q) (t : sizeTwoAllowedDifference q a) :
    Function.Injective
      (sizeTwoCyclicBaseResolvedCommonTarget_toCommonRoute code x d t) := by
  classical
  intro p w hpw
  rcases p with ⟨y, u, pl, pr⟩
  rcases w with ⟨z, v, wl, wr⟩
  have htarget :
      sizeTwoCyclicCellAt q a y u = sizeTwoCyclicCellAt q a z v :=
    congrArg SizeTwoSameDifferenceCommonRoute.target hpw
  have hcoords := congrArg (sizeTwoCyclicExteriorCellEquiv q a) htarget
  have hy : y = z := by
    simpa [sizeTwoCyclicExteriorCellEquiv_cellAt] using congrArg Prod.fst hcoords
  have hu : u = v := by
    simpa [sizeTwoCyclicExteriorCellEquiv_cellAt] using congrArg Prod.snd hcoords
  subst z
  subst v
  have hl : pl = wl :=
    (Fintype.card_le_one_iff.mp
      (sizeTwoCyclicBaseResolvedRoute_card_le_one code x t y u)) pl wl
  have hr : pr = wr :=
    (Fintype.card_le_one_iff.mp
      (sizeTwoCyclicBaseResolvedRoute_card_le_one code (x + d) t y u)) pr wr
  subst wl
  subst wr
  rfl

/-- Numerical row-inner-product form of the cap. -/
theorem sizeTwoCyclicBaseResolvedRoute_row_innerProduct_le_one
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicSameDifferenceCode q a)
    (x d : ZMod q) (hd : d ≠ 0)
    (t : sizeTwoAllowedDifference q a) :
    (∑ y : ZMod q, ∑ u : sizeTwoAllowedDifference q a,
      Fintype.card (SizeTwoCyclicBaseResolvedRoute
        code.toReciprocalCode x t y u) *
      Fintype.card (SizeTwoCyclicBaseResolvedRoute
        code.toReciprocalCode (x + d) t y u)) ≤ 1 := by
  calc
    _ = Fintype.card
        (Σ y : ZMod q, Σ u : sizeTwoAllowedDifference q a,
          (SizeTwoCyclicBaseResolvedRoute code.toReciprocalCode x t y u ×
            SizeTwoCyclicBaseResolvedRoute
              code.toReciprocalCode (x + d) t y u)) := by
      rw [Fintype.card_sigma]
      simp only [Fintype.card_prod, Fintype.card_sigma]
    _ ≤
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
  Erdos85.sizeTwoCyclicBaseResolvedRoute_row_innerProduct_le_one
