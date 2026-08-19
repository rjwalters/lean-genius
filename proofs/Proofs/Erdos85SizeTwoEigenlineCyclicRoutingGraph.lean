import Proofs.Erdos85SizeTwoEigenlineCyclicRoutingPermutation

/-!
# The routing equivalence as an adjacency graph

The explicit routing equivalence is useful only once its graph is identified
with the original exterior adjacency relation.  This file provides that exact
characterization in relative row/column coordinates.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- A source cell routes admissible relative row `r` to admissible relative
column `c` when some allowed target difference realizes both coordinates and
is adjacent to the source. -/
def sizeTwoCyclicRoutingRel
    (q : ℕ) (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a))
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1)
    (c : SizeTwoAdmissibleTargetColumn q) : Prop :=
  ∃ s : sizeTwoAllowedDifference q a, c.1 = r.1 + s.1 ∧
    C.Adj (sizeTwoCyclicCellAt q a x t)
      (sizeTwoCyclicCellAt q a (x + r.1) s)

/-- **Graph characterization of the routing permutation.** -/
theorem sizeTwoCyclicRoutingRel_iff_routingEquiv
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1)
    (routes : SizeTwoCyclicRoutingConstraints q a C)
    (x : ZMod q) (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1)
    (c : SizeTwoAdmissibleTargetColumn q) :
    sizeTwoCyclicRoutingRel q a C x t r c ↔
      sizeTwoCyclicRoutingEquiv q a C hrow_hit hcol_hit routes x t r = c := by
  let s := sizeTwoCyclicRowRoute q a C routes x t r
  have hs := sizeTwoCyclicRowRoute_spec q a C routes x t r
  constructor
  · rintro ⟨s', hcol, hadj⟩
    have hss : s' = s :=
      (Classical.choose_spec (routes.row x t r.1 r.2)).2 s' hadj
    apply Subtype.ext
    change r.1 + s.1 = c.1
    rw [← hss]
    exact hcol.symm
  · intro heq
    refine ⟨s, ?_, hs⟩
    have hval := congrArg Subtype.val heq
    change (sizeTwoCyclicRoutingEquiv
      q a C hrow_hit hcol_hit routes x t r).1 = c.1 at hval
    simpa [sizeTwoCyclicRoutingEquiv,
      sizeTwoCyclicRowRouteTargetColumn, s] using hval.symm

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicRoutingRel_iff_routingEquiv
