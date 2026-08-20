import Proofs.Erdos85SingleCollisionMultiplicityProfile
import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationInvolution

/-!
# Reciprocity between target-difference fiber blocks

Node: `BinarySizeTwoCyclicPackingBound` beneath outline A.5.3
`GAP A-REG-NONBIP`.

The local multiplicity vector records routes from a fixed source cell into
each target-difference fiber.  Here those routes are aggregated over the
source base coordinate.  Route reversal gives an exact equivalence between
the `t → u` and `u → t` blocks, retaining the positional information needed
to couple duplicate/missing defects across rows.
-/

namespace Erdos85

noncomputable section

/-- All routed darts from source-difference fiber `t` to target-difference
fiber `u`, aggregated over the cyclic source base. -/
def SizeTwoCyclicTargetFiberRoute
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (t u : sizeTwoAllowedDifference q a) :=
  {e : SizeTwoCyclicRouteDart q a code //
    e.1.2.1 = t ∧
      code.targetDifference e.1.1 e.1.2.1 ⟨e.1.2.2, e.2⟩ = u}

noncomputable instance SizeTwoCyclicRouteDart.instFintype
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a) :
    Fintype (SizeTwoCyclicRouteDart q a code) := by
  unfold SizeTwoCyclicRouteDart
  infer_instance

noncomputable instance SizeTwoCyclicTargetFiberRoute.instFintype
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (t u : sizeTwoAllowedDifference q a) :
    Fintype (SizeTwoCyclicTargetFiberRoute code t u) := by
  classical
  unfold SizeTwoCyclicTargetFiberRoute
  infer_instance

/-- Reversing every route transposes its source and target difference
fibers. -/
def sizeTwoCyclicTargetFiberRouteReverseEquiv
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (t u : sizeTwoAllowedDifference q a) :
    SizeTwoCyclicTargetFiberRoute code t u ≃
      SizeTwoCyclicTargetFiberRoute code u t where
  toFun p := by
    refine ⟨p.1.reverse, ?_⟩
    rcases p with ⟨⟨⟨x, s, r⟩, hr⟩, hsource, htarget⟩
    change s = t at hsource
    subst s
    constructor
    · simpa [SizeTwoCyclicRouteDart.reverse] using htarget
    · simpa [SizeTwoCyclicRouteDart.reverse] using
        (code.reverse_targetDifference x t ⟨r, hr⟩)
  invFun p := by
    refine ⟨p.1.reverse, ?_⟩
    rcases p with ⟨⟨⟨x, s, r⟩, hr⟩, hsource, htarget⟩
    change s = u at hsource
    subst s
    constructor
    · simpa [SizeTwoCyclicRouteDart.reverse] using htarget
    · simpa [SizeTwoCyclicRouteDart.reverse] using
        (code.reverse_targetDifference x u ⟨r, hr⟩)
  left_inv p := by
    apply Subtype.ext
    exact p.1.reverse_reverse
  right_inv p := by
    apply Subtype.ext
    exact p.1.reverse_reverse

/-- Aggregate route counts between difference fibers form a symmetric
matrix. -/
theorem sizeTwoCyclicTargetFiberRoute_card_symm
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (t u : sizeTwoAllowedDifference q a) :
    Fintype.card (SizeTwoCyclicTargetFiberRoute code t u) =
      Fintype.card (SizeTwoCyclicTargetFiberRoute code u t) :=
  Fintype.card_congr (sizeTwoCyclicTargetFiberRouteReverseEquiv code t u)

/-- The route-block cardinality is the sum of the source-local target-fiber
multiplicities. -/
theorem sizeTwoCyclicTargetFiberRoute_card_eq_multiplicity_sum
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (t u : sizeTwoAllowedDifference q a) :
    Fintype.card (SizeTwoCyclicTargetFiberRoute code t u) =
      ∑ x : ZMod q, sizeTwoCyclicTargetDifferenceMultiplicity code x t u := by
  classical
  let LocalRoute := Σ x : ZMod q,
    {r : SizeTwoAdmissibleTargetRow q t.1 //
      code.targetDifference x t r = u}
  let routeEquiv : SizeTwoCyclicTargetFiberRoute code t u ≃ LocalRoute := {
    toFun := fun p => by
      rcases p with ⟨⟨⟨x, s, r⟩, hr⟩, hsource, htarget⟩
      change s = t at hsource
      subst s
      exact ⟨x, ⟨⟨r, hr⟩, htarget⟩⟩
    invFun := fun p => by
      rcases p with ⟨x, ⟨r, htarget⟩⟩
      exact ⟨⟨(x, (t, r.1)), r.2⟩, rfl, htarget⟩
    left_inv := fun p => by
      rcases p with ⟨⟨⟨x, s, r⟩, hr⟩, hsource, htarget⟩
      change s = t at hsource
      subst s
      rfl
    right_inv := fun p => by
      rcases p with ⟨x, ⟨r, htarget⟩⟩
      rfl }
  calc
    Fintype.card (SizeTwoCyclicTargetFiberRoute code t u) =
        Fintype.card LocalRoute := Fintype.card_congr routeEquiv
    _ = ∑ x : ZMod q,
        Fintype.card {r : SizeTwoAdmissibleTargetRow q t.1 //
          code.targetDifference x t r = u} := Fintype.card_sigma
    _ = ∑ x : ZMod q,
        sizeTwoCyclicTargetDifferenceMultiplicity code x t u := by
      apply Finset.sum_congr rfl
      intro x _
      unfold sizeTwoCyclicTargetDifferenceMultiplicity
      rw [Fintype.card_subtype, Finset.card_filter]

/-- Aggregate local multiplicities transpose exactly under reciprocity. -/
theorem sizeTwoCyclicTargetDifferenceMultiplicity_sum_symm
    {q : ℕ} [NeZero q] {a : ZMod q}
    (code : SizeTwoCyclicReciprocalPermutationCode q a)
    (t u : sizeTwoAllowedDifference q a) :
    (∑ x : ZMod q,
      sizeTwoCyclicTargetDifferenceMultiplicity code x t u) =
    ∑ x : ZMod q,
      sizeTwoCyclicTargetDifferenceMultiplicity code x u t := by
  rw [← sizeTwoCyclicTargetFiberRoute_card_eq_multiplicity_sum code t u,
    ← sizeTwoCyclicTargetFiberRoute_card_eq_multiplicity_sum code u t]
  exact sizeTwoCyclicTargetFiberRoute_card_symm code t u

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicTargetFiberRoute_card_symm
#print axioms
  Erdos85.sizeTwoCyclicTargetDifferenceMultiplicity_sum_symm
