import Proofs.Erdos85MuThreeMixedGridRowRoute

/-!
# Neighborhood equivalences for the mixed-grid route code

For each occupied cell, its six allowed target rows are canonically
equivalent to its six exterior neighbours.  This is the finite-type form of
the partial-permutation representation.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Rows in which `u` is required to have an exterior neighbour. -/
def mixedGridAllowedRow
    {X Y : Type*} (H : X → Y → Prop)
    {K : X → Y → Prop} (u : muThreeMixedCell K) :=
  {x : X // ¬ H x u.1.2}

instance mixedGridAllowedRowFintype
    {X Y : Type*} [Fintype X] (H : X → Y → Prop) [DecidableRel H]
    {K : X → Y → Prop} (u : muThreeMixedCell K) :
    Fintype (mixedGridAllowedRow H u) := by
  unfold mixedGridAllowedRow
  infer_instance

/-- Any actual neighbour supplies an allowed target row. -/
theorem mixedGrid_neighbor_row_allowed
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u v : muThreeMixedCell K) (huv : C.Adj u v) :
    ¬ H v.1.1 u.1.2 := by
  rw [← MuThreeMixedGridCode.existsUnique_row_neighbor_iff H K C code]
  refine ⟨v, ⟨huv, rfl⟩, ?_⟩
  intro w hw
  by_contra hvw
  have hsep := code.rook u v w huv hw.1 (Ne.symm hvw)
  exact hsep.1 hw.2.symm

/-- The canonical equivalence between allowed rows and neighbours of `u`. -/
noncomputable def mixedGridRowRouteEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) :
    mixedGridAllowedRow H u ≃ {v : muThreeMixedCell K // v ∈ C.neighborSet u} where
  toFun x := ⟨mixedGridRowRoute H K C code u x.1 x.2,
    mixedGridRowRoute_adj H K C code u x.1 x.2⟩
  invFun v := ⟨v.1.1.1, mixedGrid_neighbor_row_allowed H K C code u v.1 v.2⟩
  left_inv x := by
    apply Subtype.ext
    exact mixedGridRowRoute_row H K C code u x.1 x.2
  right_inv v := by
    apply Subtype.ext
    exact mixedGridRowRoute_eq_of_adj_of_row H K C code u v.1 v.1.1.1
      (mixedGrid_neighbor_row_allowed H K C code u v.1 v.2) v.2 rfl

/-- Exactly six rows are allowed at every cell. -/
theorem MuThreeMixedGridCode.card_allowedRow_eq_six
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) :
    Fintype.card (mixedGridAllowedRow H u) = 6 := by
  rw [Fintype.card_congr (mixedGridRowRouteEquiv H K C code u),
    Fintype.card_subtype]
  have heq : (Finset.univ.filter fun v : muThreeMixedCell K =>
      v ∈ C.neighborSet u) = C.neighborFinset u := by
    ext v
    simp
  rw [heq, C.card_neighborFinset_eq_degree,
    MuThreeMixedGridCode.degree_eq_six H K C code u]

/-- The output-column coordinate of the route equivalence is injective. -/
theorem mixedGridRowRouteEquiv_column_injective
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) :
    Function.Injective (fun x : mixedGridAllowedRow H u =>
      ((mixedGridRowRouteEquiv H K C code u x).1.1.2)) := by
  intro x y hcol
  apply Subtype.ext
  by_contra hxy
  exact mixedGridRowRoute_column_injective H K C code u x.1 y.1
    x.2 y.2 hxy hcol

/-- Agreement rows for two source cells, stated without dependent proof
arguments in the outer predicate. -/
def mixedGridRouteAgreementRows
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u v : muThreeMixedCell K) : Finset X :=
  Finset.univ.filter fun x =>
    ∃ (hux : ¬ H x u.1.2) (hvx : ¬ H x v.1.2),
      mixedGridRowRoute H K C code u x hux =
        mixedGridRowRoute H K C code v x hvx

/-- **Finite agreement bound.** Distinct source cells agree in at most one
target row. -/
theorem mixedGridRouteAgreementRows_card_le_one
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u v : muThreeMixedCell K) (huv : u ≠ v) :
    (mixedGridRouteAgreementRows H K C code u v).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_filter.mp hy).2
  obtain ⟨hux, hvx, hxagree⟩ := hx'
  obtain ⟨huy, hvy, hyagree⟩ := hy'
  exact mixedGridRowRoute_agreement_unique H K C code u v huv x y
    hux hvx huy hvy hxagree hyagree

end

end Erdos85

#print axioms Erdos85.mixedGridRowRouteEquiv
#print axioms Erdos85.MuThreeMixedGridCode.card_allowedRow_eq_six
#print axioms Erdos85.mixedGridRowRouteEquiv_column_injective
#print axioms Erdos85.mixedGridRouteAgreementRows_card_le_one
