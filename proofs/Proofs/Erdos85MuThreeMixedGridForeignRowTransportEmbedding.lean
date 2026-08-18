import Proofs.Erdos85MuThreeMixedGridForeignRowTransport

/-!
# Simultaneous row-transport embedding

For fixed distinct endpoint columns and one source cell, all rows eligible to
both columns give distinct transported target cells.  Thus the common
eligible-row set embeds into the six-cell target fiber.  Its cardinality is
`4`, `5`, or `6` according as the two H-neighborhoods overlap in `0`, `1`, or
`2` rows; the six-row case is the saturated monodromy regime.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Common H-eligible rows for two endpoint columns. -/
def commonForeignRows {X Y : Type*} (H : X → Y → Prop) (b b' : Y) :=
  {x : X // ¬ H x b ∧ ¬ H x b'}

/-- At a fixed source cell, row transport embeds all common eligible rows
into the target column fiber. -/
noncomputable def MuThreeMixedGridCode.foreignRowTransportOutputEmbedding
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {b b' : Y} (hbb' : b ≠ b')
    (u : {u : muThreeMixedCell K // u.1.2 = b}) :
    commonForeignRows H b b' ↪ {w : muThreeMixedCell K // w.1.2 = b'} where
  toFun x := code.foreignRowTransportEquiv H K C x.1 b b'
    x.2.1 x.2.2 u
  inj' := by
    intro x z hxz
    apply Subtype.ext
    by_contra hxzVal
    exact (code.foreignRowTransportEquiv_ne H K C hxzVal hbb'
      x.2.1 x.2.2 z.2.1 z.2.2 u) hxz

/-- Explicit pairwise form of the simultaneous embedding. -/
theorem MuThreeMixedGridCode.foreignRowTransportOutput_pairwise_ne
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {b b' : Y} (hbb' : b ≠ b')
    (u : {u : muThreeMixedCell K // u.1.2 = b})
    {x z : commonForeignRows H b b'} (hxz : x ≠ z) :
    code.foreignRowTransportEquiv H K C x.1 b b' x.2.1 x.2.2 u ≠
      code.foreignRowTransportEquiv H K C z.1 b b' z.2.1 z.2.2 u := by
  exact (code.foreignRowTransportOutputEmbedding H K C hbb' u).injective.ne hxz

end


end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRowTransportOutputEmbedding
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRowTransportOutput_pairwise_ne
