import Proofs.Erdos85SizeTwoEigenlineCyclicCentralFiberSubsystem

/-!
# A loopless single-fiber packing target

Node: `SIZE-TWO-EIGENLINE(q)`, beneath `GAP A-REG-NONBIP`.

The exterior graph is simple, so its reciprocal routing code is loopless.
Consequently the graph-facing argument does not need the stronger conjecture
that even loop-permitting same-difference codes are empty.  It is enough that
for every binary parameter one allowed difference fiber forces a self-route.

This file states that weaker q-generic target and supplies its exact consumer.
No exclusion theorem is asserted here.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- At parameters `q,a`, some allowed difference fiber already excludes a
loopless reciprocal code when only its same-fiber agreement cap is retained. -/
def SizeTwoCyclicLooplessSingleFiberExclusion
    (q : ℕ) [NeZero q] (a : ZMod q) : Prop :=
  ∃ t : sizeTwoAllowedDifference q a,
    IsEmpty (SizeTwoCyclicLooplessSingleFiberCode q a t)

/-- Binary-family form of the weaker packing target sufficient for the
exterior-graph application. -/
def BinarySizeTwoCyclicLooplessSingleFiberBound : Prop :=
  ∀ (k : ℕ), 3 ≤ k →
    let q := 2 ^ k
    ∀ a : ZMod q, a ≠ 0 → a ≠ -1 →
      SizeTwoCyclicLooplessSingleFiberExclusion q a

/-- A hypothetical exterior grid yields a loopless single-fiber code in every
allowed fiber, contradicting the exclusion in any one of them. -/
theorem false_of_sizeTwoCyclicLooplessSingleFiberExclusion
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q a) C)
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1)
    (hpack : SizeTwoCyclicLooplessSingleFiberExclusion q a) : False := by
  obtain ⟨t, ht⟩ := hpack
  let code := sizeTwoCyclicExactPermutationCode_of_grid
    q a C hfree hrow_hit hcol_hit
  exact ht.false (code.toSingleFiberCode t)

end

end Erdos85

#print axioms Erdos85.false_of_sizeTwoCyclicLooplessSingleFiberExclusion
