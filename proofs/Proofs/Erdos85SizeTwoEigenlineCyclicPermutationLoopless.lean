import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationReciprocity

/-!
# Looplessness in the graph-free cyclic permutation code

Reciprocity records symmetry but does not by itself exclude a directed route
fixed by reversal.  A simple graph also forbids the route `r=0`, `s=t`, which
would send a cell to itself.  This file retains that missing invariant.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The route selected from an actual simple graph never returns to its
source cell. -/
theorem sizeTwoCyclicRowRoute_not_self
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1) :
    r.1 ≠ 0 ∨ sizeTwoCyclicRowRoute q a C routes x t r ≠ t := by
  by_contra h
  push Not at h
  obtain ⟨hr, hs⟩ := h
  have hadj := sizeTwoCyclicRowRoute_spec q a C routes x t r
  exact C.ne_of_adj hadj (by
    apply Subtype.ext
    simp [hr, hs])

/-- The graph-free reciprocal code augmented by the no-self-route law. -/
structure SizeTwoCyclicLooplessReciprocalPermutationCode
    (q : ℕ) [NeZero q] (a : ZMod q) where
  toReciprocalCode : SizeTwoCyclicReciprocalPermutationCode q a
  loopless : ∀ (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1),
      r.1 ≠ 0 ∨ toReciprocalCode.targetDifference x t r ≠ t

/-- Every hypothetical exterior grid yields a loopless reciprocal code. -/
def sizeTwoCyclicLooplessReciprocalPermutationCode_of_grid
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q a) C)
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1) :
    SizeTwoCyclicLooplessReciprocalPermutationCode q a := by
  let routes := sizeTwoCyclicRoutingConstraints_of_hits
    q a C hrow_hit hcol_hit
  let code := sizeTwoCyclicReciprocalPermutationCode_of_grid
    q a C hfree hrow_hit hcol_hit
  refine ⟨code, ?_⟩
  intro x t r
  simpa [code, routes,
    sizeTwoCyclicReciprocalPermutationCode_of_grid] using
      (sizeTwoCyclicRowRoute_not_self q a C routes x t r)

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicRowRoute_not_self
#print axioms Erdos85.sizeTwoCyclicLooplessReciprocalPermutationCode_of_grid
