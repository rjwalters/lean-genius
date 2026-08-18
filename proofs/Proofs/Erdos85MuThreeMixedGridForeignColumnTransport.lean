import Proofs.Erdos85MuThreeMixedGridForeignFiberMatching

/-!
# Column transport and C4 disagreement

This is the row/column dual of foreign row transport.  Composing through an
H-eligible column transports one occupied row fiber to another.  Between
distinct endpoint rows, transports through distinct eligible columns must
disagree pointwise, or else their two intermediate cells form a C4.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Transport between two occupied row fibers through an H-eligible column. -/
noncomputable def MuThreeMixedGridCode.foreignColumnTransportEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (y : Y) (a a' : X) (hay : ¬ H a y) (ha'y : ¬ H a' y) :
    {u : muThreeMixedCell K // u.1.1 = a} ≃
      {w : muThreeMixedCell K // w.1.1 = a'} :=
  (code.foreignFiberMatchingEquiv H K C a y hay).symm.trans
    (code.foreignFiberMatchingEquiv H K C a' y ha'y)

/-- The source row-cell is adjacent to the intermediate column-cell. -/
theorem MuThreeMixedGridCode.foreignColumnTransport_source_adj_intermediate
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (y : Y) (a : X) (hay : ¬ H a y)
    (u : {u : muThreeMixedCell K // u.1.1 = a}) :
    C.Adj u.1
      ((code.foreignFiberMatchingEquiv H K C a y hay).symm u).1 :=
  code.foreignFiberMatchingEquiv_symm_adj H K C a y hay u

/-- The intermediate column-cell is adjacent to the transported target. -/
theorem MuThreeMixedGridCode.foreignColumnTransport_intermediate_adj_target
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (y : Y) (a a' : X) (hay : ¬ H a y) (ha'y : ¬ H a' y)
    (u : {u : muThreeMixedCell K // u.1.1 = a}) :
    C.Adj ((code.foreignFiberMatchingEquiv H K C a y hay).symm u).1
      (code.foreignColumnTransportEquiv H K C y a a' hay ha'y u).1 := by
  exact code.foreignFiberMatchingEquiv_adj H K C a' y ha'y
    ((code.foreignFiberMatchingEquiv H K C a y hay).symm u)

/-- **Column-transport C4 compatibility.**  Between two distinct row fibers,
the transports through distinct common eligible columns differ pointwise. -/
theorem MuThreeMixedGridCode.foreignColumnTransportEquiv_ne
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {y t : Y} (hyt : y ≠ t) {a a' : X} (haa' : a ≠ a')
    (hay : ¬ H a y) (ha'y : ¬ H a' y)
    (hat : ¬ H a t) (ha't : ¬ H a' t)
    (u : {u : muThreeMixedCell K // u.1.1 = a}) :
    code.foreignColumnTransportEquiv H K C y a a' hay ha'y u ≠
      code.foreignColumnTransportEquiv H K C t a a' hat ha't u := by
  intro htransport
  let vy := (code.foreignFiberMatchingEquiv H K C a y hay).symm u
  let vt := (code.foreignFiberMatchingEquiv H K C a t hat).symm u
  let wy := code.foreignColumnTransportEquiv H K C y a a' hay ha'y u
  let wt := code.foreignColumnTransportEquiv H K C t a a' hat ha't u
  have huw : u.1 ≠ wy.1 := by
    intro h
    apply haa'
    calc
      a = u.1.1.1 := u.2.symm
      _ = wy.1.1.1 := congrArg (fun q : muThreeMixedCell K => q.1.1) h
      _ = a' := wy.2
  have hvyt : vy.1 ≠ vt.1 := by
    intro h
    apply hyt
    calc
      y = vy.1.1.2 := vy.2.symm
      _ = vt.1.1.2 := congrArg (fun q : muThreeMixedCell K => q.1.2) h
      _ = t := vt.2
  have htwy : C.Adj vt.1 wy.1 := by
    have ht := code.foreignColumnTransport_intermediate_adj_target
      H K C t a a' hat ha't u
    exact (congrArg Subtype.val htransport).symm ▸ ht
  apply code.c4Free
  exact containsC4_of_two_common huw hvyt
    (C.adj_symm (code.foreignColumnTransport_source_adj_intermediate
      H K C y a hay u))
    (code.foreignColumnTransport_intermediate_adj_target
      H K C y a a' hay ha'y u)
    (C.adj_symm (code.foreignColumnTransport_source_adj_intermediate
      H K C t a hat u))
    htwy

end


end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.foreignColumnTransportEquiv
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignColumnTransport_source_adj_intermediate
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignColumnTransport_intermediate_adj_target
#print axioms Erdos85.MuThreeMixedGridCode.foreignColumnTransportEquiv_ne
