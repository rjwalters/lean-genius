import Proofs.Erdos85MuThreeMixedGridForeignPermutationRookDisagreement

/-!
# Fixed-column transversals of the foreign permutations

Fix a grid column `b` and a row `x` with `¬ H x b`.  Evaluating the foreign
permutation of each occupied center in column `b` at `x` gives pairwise
distinct occupied columns in row `x`.  This is the Latin/transversal form of
same-column zero agreement.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- For a fixed center-column and eligible input row, foreign outputs embed
the occupied centers of that column into the occupied cells of the input
row. -/
noncomputable def MuThreeMixedGridCode.foreignColumnTransversalEmbedding
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (b : Y) (x : X) (hxb : ¬ H x b) :
    {u : muThreeMixedCell K // u.1.2 = b} ↪ {y : Y // ¬ K x y} where
  toFun u := by
    have hxu : ¬ H x u.1.1.2 := by simpa [u.2] using hxb
    let v := code.foreignRowNeighbor H K C u.1 ⟨x, hxu⟩
    let y := (code.foreignRowColumnEquiv H K C u.1 ⟨x, hxu⟩).1
    refine ⟨y, ?_⟩
    have hvK : ¬ K v.1.1 v.1.2 := v.2
    have hvRow := (code.foreignRowNeighbor_spec H K C u.1 ⟨x, hxu⟩).2
    have hvColumn := code.foreignRowColumnEquiv_value H K C u.1 ⟨x, hxu⟩
    exact fun hK => hvK (by simpa [v, y, hvRow, hvColumn] using hK)
  inj' := by
    intro u w huw
    apply Subtype.ext
    by_contra hne
    have hxu : ¬ H x u.1.1.2 := by simpa [u.2] using hxb
    have hxw : ¬ H x w.1.1.2 := by simpa [w.2] using hxb
    have hcolumn : u.1.1.2 = w.1.1.2 := u.2.trans w.2.symm
    have hdisagree := code.foreignRowColumnEquiv_ne_of_same_column H K C
      hne hcolumn x hxu hxw
    exact hdisagree (congrArg Subtype.val huw)

/-- The fixed-column embedding is onto: a target cell `(x,y)` chooses its
unique exterior neighbor in column `b`. -/
theorem MuThreeMixedGridCode.foreignColumnTransversalEmbedding_surjective
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (b : Y) (x : X) (hxb : ¬ H x b) :
    Function.Surjective (code.foreignColumnTransversalEmbedding H K C b x hxb) := by
  intro y
  let v : muThreeMixedCell K := ⟨(x, y.1), y.2⟩
  let u := code.foreignColumnNeighbor H K C v ⟨b, hxb⟩
  have huColumn := (code.foreignColumnNeighbor_spec H K C v ⟨b, hxb⟩).2
  let uc : {u : muThreeMixedCell K // u.1.2 = b} := ⟨u, huColumn⟩
  refine ⟨uc, ?_⟩
  apply Subtype.ext
  change (code.foreignRowColumnEquiv H K C u
    ⟨x, by simpa [u, huColumn] using hxb⟩).1 = y.1
  have hvu : C.Adj u v :=
    C.adj_symm (code.foreignColumnNeighbor_spec H K C v ⟨b, hxb⟩).1
  have hperm := code.foreignRowColumnEquiv_of_adj H K C hvu
  simpa [v] using congrArg Subtype.val hperm

/-- Exact transversal equivalence: the occupied centers in column `b` are
bijective with the occupied columns in every `H`-eligible row `x`. -/
noncomputable def MuThreeMixedGridCode.foreignColumnTransversalEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (b : Y) (x : X) (hxb : ¬ H x b) :
    {u : muThreeMixedCell K // u.1.2 = b} ≃ {y : Y // ¬ K x y} :=
  Equiv.ofBijective
    (code.foreignColumnTransversalEmbedding H K C b x hxb)
    ⟨(code.foreignColumnTransversalEmbedding H K C b x hxb).injective,
      code.foreignColumnTransversalEmbedding_surjective H K C b x hxb⟩

/-- Distinct occupied centers in one column produce distinct foreign outputs
at every row eligible for that column. -/
theorem MuThreeMixedGridCode.foreignColumnTransversal_pairwise_ne
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {u w : muThreeMixedCell K} (huw : u ≠ w)
    (hcolumn : u.1.2 = w.1.2) (x : X) (hxu : ¬ H x u.1.2) :
    (code.foreignRowColumnEquiv H K C u ⟨x, hxu⟩).1 ≠
      (code.foreignRowColumnEquiv H K C w
        ⟨x, by simpa [← hcolumn] using hxu⟩).1 := by
  exact code.foreignRowColumnEquiv_ne_of_same_column H K C
    huw hcolumn x hxu (by simpa [← hcolumn] using hxu)

end

end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.foreignColumnTransversalEmbedding
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignColumnTransversalEmbedding_surjective
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignColumnTransversalEquiv
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignColumnTransversal_pairwise_ne
