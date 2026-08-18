import Proofs.Erdos85MuThreeMixedGridRouteEquiv

/-!
# The six-point partial permutation at a mixed-grid cell

The canonical row route does more than enumerate the six neighbours of a
cell.  Projection to the output column identifies it with a bijection from
the six `H`-allowed rows to the six `H`-allowed columns.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Columns in which `u` is required to have an exterior neighbour. -/
def mixedGridAllowedColumn
    {X Y : Type*} (H : X → Y → Prop)
    {K : X → Y → Prop} (u : muThreeMixedCell K) :=
  {y : Y // ¬ H u.1.1 y}

instance mixedGridAllowedColumnFintype
    {X Y : Type*} [Fintype Y] (H : X → Y → Prop) [DecidableRel H]
    {K : X → Y → Prop} (u : muThreeMixedCell K) :
    Fintype (mixedGridAllowedColumn H u) := by
  unfold mixedGridAllowedColumn
  infer_instance

/-- Any actual neighbour supplies an allowed target column. -/
theorem mixedGrid_neighbor_column_allowed
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u v : muThreeMixedCell K) (huv : C.Adj u v) :
    ¬ H u.1.1 v.1.2 := by
  rw [← MuThreeMixedGridCode.existsUnique_column_neighbor_iff H K C code]
  refine ⟨v, ⟨huv, rfl⟩, ?_⟩
  intro w hw
  by_contra hvw
  have hsep := code.rook u v w huv hw.1 (Ne.symm hvw)
  exact hsep.2 hw.2.symm

/-- Exactly six columns are allowed at every cell. -/
theorem MuThreeMixedGridCode.card_allowedColumn_eq_six
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) :
    Fintype.card (mixedGridAllowedColumn H u) = 6 := by
  change Fintype.card {y : Y // ¬ H u.1.1 y} = 6
  rw [Fintype.card_subtype]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset Y)) (p := fun y => H u.1.1 y)
  simp only [Finset.card_univ, code.card_right] at hpartition
  rw [code.H_twoRegular.1 u.1.1] at hpartition
  omega

/-- Output-column projection of the canonical row route. -/
noncomputable def mixedGridRowPermutationFun
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) :
    mixedGridAllowedRow H u → mixedGridAllowedColumn H u := fun x =>
  ⟨(mixedGridRowRoute H K C code u x.1 x.2).1.2,
    mixedGrid_neighbor_column_allowed H K C code u _
      (mixedGridRowRoute_adj H K C code u x.1 x.2)⟩

theorem mixedGridRowPermutationFun_injective
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) :
    Function.Injective (mixedGridRowPermutationFun H K C code u) := by
  intro x y hxy
  apply Subtype.ext
  by_contra hne
  exact mixedGridRowRoute_column_injective H K C code u x.1 y.1
    x.2 y.2 hne (congrArg Subtype.val hxy)

/-- Every occupied cell canonically carries a permutation between its six
allowed target rows and its six allowed target columns. -/
noncomputable def mixedGridRowPermutation
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) :
    mixedGridAllowedRow H u ≃ mixedGridAllowedColumn H u := by
  refine Equiv.ofBijective (mixedGridRowPermutationFun H K C code u) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨mixedGridRowPermutationFun_injective H K C code u,
    (code.card_allowedRow_eq_six H K C u).trans
      (code.card_allowedColumn_eq_six H K C u).symm⟩

theorem mixedGridRowPermutation_apply
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : mixedGridAllowedRow H u) :
    (mixedGridRowPermutation H K C code u x).1 =
      (mixedGridRowRoute H K C code u x.1 x.2).1.2 := rfl

end


end Erdos85

#print axioms Erdos85.mixedGridRowPermutation
#print axioms Erdos85.mixedGridRowPermutation_apply
