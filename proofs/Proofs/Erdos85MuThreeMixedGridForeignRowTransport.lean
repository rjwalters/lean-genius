import Proofs.Erdos85MuThreeMixedGridForeignFiberMatching

/-!
# Row transport and C4 disagreement

Composing the matching from column `b` to row `x` with the inverse matching
from column `b'` to that row transports the six-cell fiber of `b` to the
six-cell fiber of `b'`.  For distinct endpoint columns, transports through
two distinct eligible rows must disagree pointwise; an agreement would give
two common neighbors and hence a four-cycle.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Transport between two occupied column fibers through an H-eligible row. -/
noncomputable def MuThreeMixedGridCode.foreignRowTransportEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (x : X) (b b' : Y) (hxb : ¬ H x b) (hxb' : ¬ H x b') :
    {u : muThreeMixedCell K // u.1.2 = b} ≃
      {w : muThreeMixedCell K // w.1.2 = b'} :=
  (code.foreignFiberMatchingEquiv H K C x b hxb).trans
    (code.foreignFiberMatchingEquiv H K C x b' hxb').symm

/-- The source and the intermediate row-cell form a C-edge. -/
theorem MuThreeMixedGridCode.foreignRowTransport_source_adj_intermediate
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (x : X) (b : Y) (hxb : ¬ H x b)
    (u : {u : muThreeMixedCell K // u.1.2 = b}) :
    C.Adj u.1 (code.foreignFiberMatchingEquiv H K C x b hxb u).1 :=
  code.foreignFiberMatchingEquiv_adj H K C x b hxb u

/-- The same intermediate cell is adjacent to the transported target. -/
theorem MuThreeMixedGridCode.foreignRowTransport_intermediate_adj_target
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (x : X) (b b' : Y) (hxb : ¬ H x b) (hxb' : ¬ H x b')
    (u : {u : muThreeMixedCell K // u.1.2 = b}) :
    C.Adj (code.foreignFiberMatchingEquiv H K C x b hxb u).1
      (code.foreignRowTransportEquiv H K C x b b' hxb hxb' u).1 := by
  exact code.foreignFiberMatchingEquiv_symm_adj H K C x b' hxb'
    (code.foreignFiberMatchingEquiv H K C x b hxb u)

/-- **Row-transport C4 compatibility.**  Between two distinct column fibers,
the transports through distinct common eligible rows are pointwise
different. -/
theorem MuThreeMixedGridCode.foreignRowTransportEquiv_ne
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {x z : X} (hxz : x ≠ z) {b b' : Y} (hbb' : b ≠ b')
    (hxb : ¬ H x b) (hxb' : ¬ H x b')
    (hzb : ¬ H z b) (hzb' : ¬ H z b')
    (u : {u : muThreeMixedCell K // u.1.2 = b}) :
    code.foreignRowTransportEquiv H K C x b b' hxb hxb' u ≠
      code.foreignRowTransportEquiv H K C z b b' hzb hzb' u := by
  intro htransport
  let vx := code.foreignFiberMatchingEquiv H K C x b hxb u
  let vz := code.foreignFiberMatchingEquiv H K C z b hzb u
  let wx := code.foreignRowTransportEquiv H K C x b b' hxb hxb' u
  let wz := code.foreignRowTransportEquiv H K C z b b' hzb hzb' u
  have huw : u.1 ≠ wx.1 := by
    intro h
    apply hbb'
    calc
      b = u.1.1.2 := u.2.symm
      _ = wx.1.1.2 := congrArg (fun q : muThreeMixedCell K => q.1.2) h
      _ = b' := wx.2
  have hvxvz : vx.1 ≠ vz.1 := by
    intro h
    apply hxz
    calc
      x = vx.1.1.1 := vx.2.symm
      _ = vz.1.1.1 := congrArg (fun q : muThreeMixedCell K => q.1.1) h
      _ = z := vz.2
  have hzwx : C.Adj vz.1 wx.1 := by
    have hz := code.foreignRowTransport_intermediate_adj_target
      H K C z b b' hzb hzb' u
    exact (congrArg Subtype.val htransport).symm ▸ hz
  apply code.c4Free
  exact containsC4_of_two_common huw hvxvz
    (C.adj_symm (code.foreignRowTransport_source_adj_intermediate
      H K C x b hxb u))
    (code.foreignRowTransport_intermediate_adj_target
      H K C x b b' hxb hxb' u)
    (C.adj_symm (code.foreignRowTransport_source_adj_intermediate
      H K C z b hzb u))
    hzwx

end


end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.foreignRowTransportEquiv
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRowTransport_source_adj_intermediate
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRowTransport_intermediate_adj_target
#print axioms Erdos85.MuThreeMixedGridCode.foreignRowTransportEquiv_ne
