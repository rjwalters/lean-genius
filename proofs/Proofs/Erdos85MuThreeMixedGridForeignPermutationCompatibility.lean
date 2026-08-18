import Proofs.Erdos85MuThreeMixedGridForeignPermutation

/-!
# C4 compatibility of the mixed-grid foreign permutations

Two distinct centers cannot have their local foreign row-to-column
permutations agree at two common eligible rows.  Each agreement produces a
common exterior neighbor, so two agreements would produce a four-cycle.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- **Foreign-permutation C4 compatibility.**  At two distinct cells, the
local row-to-column permutations agree on at most one row that is eligible
for both cells. -/
theorem MuThreeMixedGridCode.foreignRowColumnEquiv_agree_at_most_one
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {u w : muThreeMixedCell K} (huw : u ≠ w)
    {x z : X} (hxz : x ≠ z)
    (hxu : ¬ H x u.1.2) (hxw : ¬ H x w.1.2)
    (hzu : ¬ H z u.1.2) (hzw : ¬ H z w.1.2)
    (hagreeX :
      (code.foreignRowColumnEquiv H K C u ⟨x, hxu⟩).1 =
        (code.foreignRowColumnEquiv H K C w ⟨x, hxw⟩).1)
    (hagreeZ :
      (code.foreignRowColumnEquiv H K C u ⟨z, hzu⟩).1 =
        (code.foreignRowColumnEquiv H K C w ⟨z, hzw⟩).1) : False := by
  let ux := code.foreignRowNeighbor H K C u ⟨x, hxu⟩
  let wx := code.foreignRowNeighbor H K C w ⟨x, hxw⟩
  let uz := code.foreignRowNeighbor H K C u ⟨z, hzu⟩
  let wz := code.foreignRowNeighbor H K C w ⟨z, hzw⟩
  have huxwx : ux = wx := by
    apply Subtype.ext
    apply Prod.ext
    · exact (code.foreignRowNeighbor_spec H K C u ⟨x, hxu⟩).2.trans
        (code.foreignRowNeighbor_spec H K C w ⟨x, hxw⟩).2.symm
    · rw [← code.foreignRowColumnEquiv_value H K C u ⟨x, hxu⟩,
        ← code.foreignRowColumnEquiv_value H K C w ⟨x, hxw⟩]
      exact hagreeX
  have huzwz : uz = wz := by
    apply Subtype.ext
    apply Prod.ext
    · exact (code.foreignRowNeighbor_spec H K C u ⟨z, hzu⟩).2.trans
        (code.foreignRowNeighbor_spec H K C w ⟨z, hzw⟩).2.symm
    · rw [← code.foreignRowColumnEquiv_value H K C u ⟨z, hzu⟩,
        ← code.foreignRowColumnEquiv_value H K C w ⟨z, hzw⟩]
      exact hagreeZ
  have huxuz : ux ≠ uz := by
    intro h
    apply hxz
    calc
      x = ux.1.1 :=
        (code.foreignRowNeighbor_spec H K C u ⟨x, hxu⟩).2.symm
      _ = uz.1.1 := congrArg (fun v : muThreeMixedCell K => v.1.1) h
      _ = z := (code.foreignRowNeighbor_spec H K C u ⟨z, hzu⟩).2
  apply code.c4Free
  exact containsC4_of_two_common huw huxuz
    (C.adj_symm (code.foreignRowNeighbor_spec H K C u ⟨x, hxu⟩).1)
    (huxwx ▸ C.adj_symm
      (code.foreignRowNeighbor_spec H K C w ⟨x, hxw⟩).1)
    (C.adj_symm (code.foreignRowNeighbor_spec H K C u ⟨z, hzu⟩).1)
    (huzwz ▸ C.adj_symm
      (code.foreignRowNeighbor_spec H K C w ⟨z, hzw⟩).1)

end

end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRowColumnEquiv_agree_at_most_one
