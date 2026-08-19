import Proofs.Erdos85SizeTwoEigenlineCyclicPermutationCode

/-!
# Reciprocity of the cyclic routing permutations

Node: `SIZE-TWO-EIGENLINE(q)`, beneath `GAP A-REG-NONBIP`.

The routing permutation code also remembers that exterior adjacency is
undirected.  If the route from `(x,t)` through relative row `r` reaches
difference `s`, then the reverse route from `(x+r,s)` through row `-r`
returns through relative column `t-r`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem sizeTwoCyclicRoutingEquiv_reciprocity
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
    (r : SizeTwoAdmissibleTargetRow q t.1) :
    let s := sizeTwoCyclicRowRoute q a C routes x t r
    let c := sizeTwoCyclicRowRouteTargetColumn
      q a C hcol_hit routes x t r
    let reverseRow : SizeTwoAdmissibleTargetRow q s.1 :=
      ⟨-r.1, by
        constructor
        · intro hs
          apply c.2.1
          have := congrArg (fun z : ZMod q => r.1 + z) hs
          simpa [c, sizeTwoCyclicRowRouteTargetColumn,
            add_assoc] using this
        · intro hs
          apply c.2.2
          have := congrArg (fun z : ZMod q => r.1 + z) hs
          simpa [c, sizeTwoCyclicRowRouteTargetColumn,
            sub_eq_add_neg, add_assoc] using this⟩
    (sizeTwoCyclicRoutingEquiv q a C hrow_hit hcol_hit routes
      (x + r.1) s reverseRow).1 = t.1 - r.1 := by
  dsimp only
  let s := sizeTwoCyclicRowRoute q a C routes x t r
  let c := sizeTwoCyclicRowRouteTargetColumn
    q a C hcol_hit routes x t r
  have hrevAdmissible : s.1 ≠ -r.1 ∧ s.1 ≠ (-r.1) - 1 := by
    constructor
    · intro hs
      apply c.2.1
      have := congrArg (fun z : ZMod q => r.1 + z) hs
      simpa [c, sizeTwoCyclicRowRouteTargetColumn,
        add_assoc] using this
    · intro hs
      apply c.2.2
      have := congrArg (fun z : ZMod q => r.1 + z) hs
      simpa [c, sizeTwoCyclicRowRouteTargetColumn,
        sub_eq_add_neg, add_assoc] using this
  let reverseRow : SizeTwoAdmissibleTargetRow q s.1 :=
    ⟨-r.1, hrevAdmissible⟩
  have hfwd := sizeTwoCyclicRowRoute_spec q a C routes x t r
  have hrev : C.Adj (sizeTwoCyclicCellAt q a (x + r.1) s)
      (sizeTwoCyclicCellAt q a ((x + r.1) + reverseRow.1) t) := by
    have := C.adj_symm hfwd
    convert this using 2
    simp [reverseRow]
  have hu := routes.row (x + r.1) s reverseRow.1 reverseRow.2
  have hsroute : sizeTwoCyclicRowRoute q a C routes
      (x + r.1) s reverseRow = t :=
    hu.unique
      (sizeTwoCyclicRowRoute_spec q a C routes (x + r.1) s reverseRow)
      hrev
  change reverseRow.1 +
      (sizeTwoCyclicRowRoute q a C routes
        (x + r.1) s reverseRow).1 = t.1 - r.1
  rw [hsroute]
  simp [reverseRow, sub_eq_add_neg, add_comm]

structure SizeTwoCyclicReciprocalPermutationCode
    (q : ℕ) [NeZero q] (a : ZMod q) where
  toPermutationCode : SizeTwoCyclicPermutationCode q a
  targetDifference : ∀ (x : ZMod q)
    (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1),
      sizeTwoAllowedDifference q a
  target_column_eq : ∀ (x : ZMod q)
    (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1),
      r.1 + (targetDifference x t r).1 =
        (toPermutationCode.perm x t r).1
  reverse_admissible : ∀ (x : ZMod q)
    (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1),
      let s := targetDifference x t r
      s.1 ≠ -r.1 ∧ s.1 ≠ (-r.1) - 1
  reciprocity : ∀ (x : ZMod q)
    (t : sizeTwoAllowedDifference q a)
    (r : SizeTwoAdmissibleTargetRow q t.1),
      let s := targetDifference x t r
      let reverseRow : SizeTwoAdmissibleTargetRow q s.1 :=
        ⟨-r.1, reverse_admissible x t r⟩
      (toPermutationCode.perm (x + r.1) s reverseRow).1 = t.1 - r.1

def sizeTwoCyclicReciprocalPermutationCode_of_grid
    (q : ℕ) [NeZero q] (a : ZMod q)
    (C : SimpleGraph (sizeTwoCyclicExteriorCell q a)) [DecidableRel C.Adj]
    (hfree : ¬ containsC4 (sizeTwoCyclicExteriorCell q a) C)
    (hrow_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (y : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.1 = y).card =
        if u.1.2 = y ∨ u.1.2 = y - 1 then 0 else 1)
    (hcol_hit : ∀ (u : sizeTwoCyclicExteriorCell q a) (z : ZMod q),
      ((C.neighborFinset u).filter fun v => v.1.2 = z).card =
        if u.1.1 = z ∨ u.1.1 = z + 1 then 0 else 1) :
    SizeTwoCyclicReciprocalPermutationCode q a := by
  let routes := sizeTwoCyclicRoutingConstraints_of_hits
    q a C hrow_hit hcol_hit
  let code := sizeTwoCyclicPermutationCode_of_grid
    q a C hfree hrow_hit hcol_hit
  refine {
    toPermutationCode := code
    targetDifference := fun x t r =>
      sizeTwoCyclicRowRoute q a C routes x t r
    target_column_eq := ?_
    reverse_admissible := ?_
    reciprocity := ?_ }
  · intro x t r
    rfl
  · intro x t r
    let s := sizeTwoCyclicRowRoute q a C routes x t r
    let c := sizeTwoCyclicRowRouteTargetColumn
      q a C hcol_hit routes x t r
    have hc : c.1 = r.1 + s.1 := rfl
    constructor
    · intro hs
      apply c.2.1
      rw [hc, hs]
      simp
    · intro hs
      apply c.2.2
      rw [hc, hs]
      simp [sub_eq_add_neg, add_assoc]
  · intro x t r
    simpa [code, routes, sizeTwoCyclicPermutationCode_of_grid] using
      (sizeTwoCyclicRoutingEquiv_reciprocity
        q a C hrow_hit hcol_hit routes x t r)

end

end Erdos85

#print axioms Erdos85.sizeTwoCyclicRoutingEquiv_reciprocity
#print axioms Erdos85.sizeTwoCyclicReciprocalPermutationCode_of_grid
