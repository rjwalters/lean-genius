import Proofs.Erdos85MuThreeMixedGridSquareMatrix

/-!
# Partial-permutation row routes in a mixed `mu = 3` grid

The row-hit law canonically presents every exterior neighbourhood as a
partial permutation: from a cell `u`, every row not forbidden by `H` contains
one neighbour.  Rook separation makes their columns distinct, symmetry gives
inverse routes, and C4-freeness says two source cells can agree in at most one
target row.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The unique neighbour of `u` in an `H`-allowed target row. -/
noncomputable def mixedGridRowRoute
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : X) (hx : ¬ H x u.1.2) :
    muThreeMixedCell K :=
  Classical.choose
    ((MuThreeMixedGridCode.existsUnique_row_neighbor_iff H K C code u x).mpr hx)

theorem mixedGridRowRoute_spec
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : X) (hx : ¬ H x u.1.2) :
    C.Adj u (mixedGridRowRoute H K C code u x hx) ∧
      (mixedGridRowRoute H K C code u x hx).1.1 = x :=
  (Classical.choose_spec
    ((MuThreeMixedGridCode.existsUnique_row_neighbor_iff H K C code u x).mpr hx)).1

theorem mixedGridRowRoute_adj
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : X) (hx : ¬ H x u.1.2) :
    C.Adj u (mixedGridRowRoute H K C code u x hx) :=
  (mixedGridRowRoute_spec H K C code u x hx).1

theorem mixedGridRowRoute_row
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : X) (hx : ¬ H x u.1.2) :
    (mixedGridRowRoute H K C code u x hx).1.1 = x :=
  (mixedGridRowRoute_spec H K C code u x hx).2

/-- Characterizing uniqueness of the selected route. -/
theorem mixedGridRowRoute_eq_of_adj_of_row
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u v : muThreeMixedCell K) (x : X) (hx : ¬ H x u.1.2)
    (huv : C.Adj u v) (hvrow : v.1.1 = x) :
    mixedGridRowRoute H K C code u x hx = v := by
  exact ((Classical.choose_spec
    ((MuThreeMixedGridCode.existsUnique_row_neighbor_iff H K C code u x).mpr hx)).2
      v ⟨huv, hvrow⟩).symm

/-- Distinct target rows give distinct target columns: the route is a partial
permutation rather than merely a choice of one cell per row. -/
theorem mixedGridRowRoute_column_injective
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x x' : X)
    (hx : ¬ H x u.1.2) (hx' : ¬ H x' u.1.2) (hxx' : x ≠ x') :
    (mixedGridRowRoute H K C code u x hx).1.2 ≠
      (mixedGridRowRoute H K C code u x' hx').1.2 := by
  let v := mixedGridRowRoute H K C code u x hx
  let w := mixedGridRowRoute H K C code u x' hx'
  have hvw : v ≠ w := by
    intro h
    apply hxx'
    have heq := congrArg (fun z : muThreeMixedCell K => z.1.1) h
    dsimp [v, w] at heq
    rw [mixedGridRowRoute_row H K C code u x hx,
      mixedGridRowRoute_row H K C code u x' hx'] at heq
    exact heq
  exact (code.rook u v w
    (mixedGridRowRoute_adj H K C code u x hx)
    (mixedGridRowRoute_adj H K C code u x' hx') hvw).2

/-- The reverse route is allowed by `H`; this follows from symmetry and rook
uniqueness, not from an additional compatibility assumption. -/
theorem mixedGridRowRoute_back_allowed
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : X) (hx : ¬ H x u.1.2) :
    let v := mixedGridRowRoute H K C code u x hx
    ¬ H u.1.1 v.1.2 := by
  dsimp
  rw [← MuThreeMixedGridCode.existsUnique_row_neighbor_iff H K C code]
  refine ⟨u, ⟨C.adj_symm (mixedGridRowRoute_adj H K C code u x hx), rfl⟩, ?_⟩
  intro w hw
  by_contra hwu
  have hsep := code.rook (mixedGridRowRoute H K C code u x hx) u w
    (C.adj_symm (mixedGridRowRoute_adj H K C code u x hx)) hw.1 (Ne.symm hwu)
  exact hsep.1 (hw.2.symm)

/-- Route symmetry: routing back to the source row returns the source cell. -/
theorem mixedGridRowRoute_inverse
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u : muThreeMixedCell K) (x : X) (hx : ¬ H x u.1.2) :
    let v := mixedGridRowRoute H K C code u x hx
    mixedGridRowRoute H K C code v u.1.1
      (mixedGridRowRoute_back_allowed H K C code u x hx) = u := by
  dsimp
  apply mixedGridRowRoute_eq_of_adj_of_row H K C code
  · exact C.adj_symm (mixedGridRowRoute_adj H K C code u x hx)
  · rfl

/-- **C4 code law.** Two distinct source cells can have equal row routes in
at most one target row. -/
theorem mixedGridRowRoute_agreement_unique
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (u v : muThreeMixedCell K) (huv : u ≠ v)
    (x y : X)
    (hux : ¬ H x u.1.2) (hvx : ¬ H x v.1.2)
    (huy : ¬ H y u.1.2) (hvy : ¬ H y v.1.2)
    (hxagree : mixedGridRowRoute H K C code u x hux =
      mixedGridRowRoute H K C code v x hvx)
    (hyagree : mixedGridRowRoute H K C code u y huy =
      mixedGridRowRoute H K C code v y hvy) : x = y := by
  let wx := mixedGridRowRoute H K C code u x hux
  let wy := mixedGridRowRoute H K C code u y huy
  have hwx : wx ∈ C.neighborFinset u ∩ C.neighborFinset v := by
    apply Finset.mem_inter.mpr
    refine ⟨(C.mem_neighborFinset u wx).mpr
      (mixedGridRowRoute_adj H K C code u x hux), ?_⟩
    apply (C.mem_neighborFinset v wx).mpr
    change C.Adj v (mixedGridRowRoute H K C code u x hux)
    rw [hxagree]
    exact mixedGridRowRoute_adj H K C code v x hvx
  have hwy : wy ∈ C.neighborFinset u ∩ C.neighborFinset v := by
    apply Finset.mem_inter.mpr
    refine ⟨(C.mem_neighborFinset u wy).mpr
      (mixedGridRowRoute_adj H K C code u y huy), ?_⟩
    apply (C.mem_neighborFinset v wy).mpr
    change C.Adj v (mixedGridRowRoute H K C code u y huy)
    rw [hyagree]
    exact mixedGridRowRoute_adj H K C code v y hvy
  have hle := MuThreeMixedGridCode.common_neighbor_card_le_one
    H K C code u v huv
  have hwxy : wx = wy := Finset.card_le_one.mp hle wx hwx wy hwy
  have heq := congrArg (fun z : muThreeMixedCell K => z.1.1) hwxy
  dsimp [wx, wy] at heq
  rw [mixedGridRowRoute_row H K C code u x hux,
    mixedGridRowRoute_row H K C code u y huy] at heq
  exact heq

end

end Erdos85

#print axioms Erdos85.mixedGridRowRoute_column_injective
#print axioms Erdos85.mixedGridRowRoute_back_allowed
#print axioms Erdos85.mixedGridRowRoute_inverse
#print axioms Erdos85.mixedGridRowRoute_agreement_unique
