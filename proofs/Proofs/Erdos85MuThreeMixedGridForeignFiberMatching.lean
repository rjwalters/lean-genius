import Proofs.Erdos85MuThreeMixedGridForeignRowTransversal

/-!
# Perfect matchings indexed by H-nonedges

Every pair `(x,b)` with `¬ H x b` indexes a perfect matching in the exterior
graph `C`: the six occupied cells of column `b` are matched bijectively to the
six occupied cells of row `x`.  The two hit-uniqueness laws are precisely the
two inverse directions of this equivalence.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The `C`-perfect matching from occupied column `b` to occupied row `x`
indexed by the H-nonedge `(x,b)`. -/
noncomputable def MuThreeMixedGridCode.foreignFiberMatchingEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (x : X) (b : Y) (hxb : ¬ H x b) :
    {u : muThreeMixedCell K // u.1.2 = b} ≃
      {v : muThreeMixedCell K // v.1.1 = x} where
  toFun u := by
    have hxu : ¬ H x u.1.1.2 := by simpa [u.2] using hxb
    exact ⟨code.foreignRowNeighbor H K C u.1 ⟨x, hxu⟩,
      (code.foreignRowNeighbor_spec H K C u.1 ⟨x, hxu⟩).2⟩
  invFun v := by
    have hvb : ¬ H v.1.1.1 b := by simpa [v.2] using hxb
    exact ⟨code.foreignColumnNeighbor H K C v.1 ⟨b, hvb⟩,
      (code.foreignColumnNeighbor_spec H K C v.1 ⟨b, hvb⟩).2⟩
  left_inv u := by
    apply Subtype.ext
    have hxu : ¬ H x u.1.1.2 := by simpa [u.2] using hxb
    let v := code.foreignRowNeighbor H K C u.1 ⟨x, hxu⟩
    have hvb : ¬ H v.1.1 b := by
      simpa [v, (code.foreignRowNeighbor_spec H K C u.1 ⟨x, hxu⟩).2]
        using hxb
    exact (code.foreignColumnNeighbor_unique H K C v ⟨b, hvb⟩ u.1
      (C.adj_symm (code.foreignRowNeighbor_spec H K C u.1 ⟨x, hxu⟩).1)
      u.2).symm
  right_inv v := by
    apply Subtype.ext
    have hvb : ¬ H v.1.1.1 b := by simpa [v.2] using hxb
    let u := code.foreignColumnNeighbor H K C v.1 ⟨b, hvb⟩
    have hxu : ¬ H x u.1.2 := by
      simpa [u, (code.foreignColumnNeighbor_spec H K C v.1 ⟨b, hvb⟩).2]
        using hxb
    exact (code.foreignRowNeighbor_unique H K C u ⟨x, hxu⟩ v.1
      (C.adj_symm (code.foreignColumnNeighbor_spec H K C v.1 ⟨b, hvb⟩).1)
      v.2).symm

/-- Every forward matching pair is an exterior edge. -/
theorem MuThreeMixedGridCode.foreignFiberMatchingEquiv_adj
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (x : X) (b : Y) (hxb : ¬ H x b)
    (u : {u : muThreeMixedCell K // u.1.2 = b}) :
    C.Adj u.1 (code.foreignFiberMatchingEquiv H K C x b hxb u).1 := by
  exact (code.foreignRowNeighbor_spec H K C u.1
    ⟨x, by simpa [u.2] using hxb⟩).1

/-- Conversely the inverse matching pair is the same exterior edge with
orientation reversed. -/
theorem MuThreeMixedGridCode.foreignFiberMatchingEquiv_symm_adj
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (x : X) (b : Y) (hxb : ¬ H x b)
    (v : {v : muThreeMixedCell K // v.1.1 = x}) :
    C.Adj v.1 ((code.foreignFiberMatchingEquiv H K C x b hxb).symm v).1 := by
  exact (code.foreignColumnNeighbor_spec H K C v.1
    ⟨b, by simpa [v.2] using hxb⟩).1

end


end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.foreignFiberMatchingEquiv
#print axioms Erdos85.MuThreeMixedGridCode.foreignFiberMatchingEquiv_adj
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignFiberMatchingEquiv_symm_adj
