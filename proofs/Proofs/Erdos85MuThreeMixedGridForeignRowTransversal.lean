import Proofs.Erdos85MuThreeMixedGridForeignColumnTransversal

/-!
# Fixed-row transversals of the foreign permutations

This is the row/column dual of the fixed-column transversal.  Fix a
center-row `a` and an `H`-eligible target column `y`.  Inverse evaluation of
the six local permutations in row `a` bijects those centers with the six
occupied rows in column `y`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem MuThreeMixedGridCode.foreignRowColumnEquiv_symm_value
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (u : muThreeMixedCell K)
    (y : {y : Y // ¬ H u.1.1 y}) :
    ((code.foreignRowColumnEquiv H K C u).symm y).1 =
      (code.foreignColumnNeighbor H K C u y).1.1 := by
  rfl

/-- Inverse evaluation embeds occupied centers of a fixed row into the
occupied rows of an eligible target column. -/
noncomputable def MuThreeMixedGridCode.foreignRowTransversalEmbedding
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a : X) (y : Y) (hay : ¬ H a y) :
    {u : muThreeMixedCell K // u.1.1 = a} ↪ {x : X // ¬ K x y} where
  toFun u := by
    have huy : ¬ H u.1.1.1 y := by simpa [u.2] using hay
    let v := code.foreignColumnNeighbor H K C u.1 ⟨y, huy⟩
    let x := ((code.foreignRowColumnEquiv H K C u.1).symm ⟨y, huy⟩).1
    refine ⟨x, ?_⟩
    have hvK : ¬ K v.1.1 v.1.2 := v.2
    have hvColumn := (code.foreignColumnNeighbor_spec H K C u.1 ⟨y, huy⟩).2
    have hvRow := code.foreignRowColumnEquiv_symm_value H K C u.1 ⟨y, huy⟩
    exact fun hK => hvK (by simpa [v, x, hvRow, hvColumn] using hK)
  inj' := by
    intro u w huw
    apply Subtype.ext
    by_contra hne
    have huy : ¬ H u.1.1.1 y := by simpa [u.2] using hay
    have hwy : ¬ H w.1.1.1 y := by simpa [w.2] using hay
    let xu := (code.foreignRowColumnEquiv H K C u.1).symm ⟨y, huy⟩
    let xw := (code.foreignRowColumnEquiv H K C w.1).symm ⟨y, hwy⟩
    have hx : xu.1 = xw.1 := congrArg Subtype.val huw
    have hxw : ¬ H xu.1 w.1.1.2 := by simpa [hx] using xw.2
    have hrow : u.1.1.1 = w.1.1.1 := u.2.trans w.2.symm
    have hdisagree := code.foreignRowColumnEquiv_ne_of_same_row H K C
      hne hrow xu.1 xu.2 hxw
    have huApply :
        (code.foreignRowColumnEquiv H K C u.1 xu).1 = y := by
      exact congrArg Subtype.val
        ((code.foreignRowColumnEquiv H K C u.1).apply_symm_apply ⟨y, huy⟩)
    have hwApply :
        (code.foreignRowColumnEquiv H K C w.1 ⟨xu.1, hxw⟩).1 = y := by
      have hxsub : (⟨xu.1, hxw⟩ : {x : X // ¬ H x w.1.1.2}) = xw :=
        Subtype.ext hx
      rw [hxsub]
      exact congrArg Subtype.val
        ((code.foreignRowColumnEquiv H K C w.1).apply_symm_apply ⟨y, hwy⟩)
    exact hdisagree (huApply.trans hwApply.symm)

/-- The row embedding is onto by the row-hit uniqueness law. -/
theorem MuThreeMixedGridCode.foreignRowTransversalEmbedding_surjective
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a : X) (y : Y) (hay : ¬ H a y) :
    Function.Surjective (code.foreignRowTransversalEmbedding H K C a y hay) := by
  intro x
  let v : muThreeMixedCell K := ⟨(x.1, y), x.2⟩
  let u := code.foreignRowNeighbor H K C v ⟨a, hay⟩
  have huRow := (code.foreignRowNeighbor_spec H K C v ⟨a, hay⟩).2
  let uc : {u : muThreeMixedCell K // u.1.1 = a} := ⟨u, huRow⟩
  refine ⟨uc, ?_⟩
  apply Subtype.ext
  have huv : C.Adj u v :=
    C.adj_symm (code.foreignRowNeighbor_spec H K C v ⟨a, hay⟩).1
  have hperm := code.foreignRowColumnEquiv_of_adj H K C huv
  have hinv := congrArg (code.foreignRowColumnEquiv H K C u).symm hperm
  change ((code.foreignRowColumnEquiv H K C u).symm
    ⟨y, by simpa [u, huRow] using hay⟩).1 = x.1
  simpa [v] using (congrArg Subtype.val hinv).symm

/-- Exact fixed-row transversal equivalence. -/
noncomputable def MuThreeMixedGridCode.foreignRowTransversalEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (a : X) (y : Y) (hay : ¬ H a y) :
    {u : muThreeMixedCell K // u.1.1 = a} ≃ {x : X // ¬ K x y} :=
  Equiv.ofBijective
    (code.foreignRowTransversalEmbedding H K C a y hay)
    ⟨(code.foreignRowTransversalEmbedding H K C a y hay).injective,
      code.foreignRowTransversalEmbedding_surjective H K C a y hay⟩

end


end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRowColumnEquiv_symm_value
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRowTransversalEmbedding
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRowTransversalEmbedding_surjective
#print axioms Erdos85.MuThreeMixedGridCode.foreignRowTransversalEquiv
