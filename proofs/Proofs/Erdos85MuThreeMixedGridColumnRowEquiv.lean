import Proofs.Erdos85MuThreeMixedGridRouteDisjoint
import Proofs.Erdos85MuThreeMixedGridSquareDegrees

/-!
# Column-to-row bijections in a mixed μ=3 grid

Fix an `H`-allowed coordinate pair `(x,y)`.  Every occupied cell in column
`y` has a unique exterior neighbour in row `x`.  Rook disjointness makes
these six neighbours distinct, so they exhaust the six occupied cells of
row `x`.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

def mixedGridOccupiedColumn
    {X Y : Type*} (K : X → Y → Prop) (y : Y) :=
  {u : muThreeMixedCell K // u.1.2 = y}

def mixedGridOccupiedRow
    {X Y : Type*} (K : X → Y → Prop) (x : X) :=
  {u : muThreeMixedCell K // u.1.1 = x}

instance mixedGridOccupiedColumnFintype
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K] (y : Y) :
    Fintype (mixedGridOccupiedColumn K y) := by
  unfold mixedGridOccupiedColumn
  infer_instance

instance mixedGridOccupiedRowFintype
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K] (x : X) :
    Fintype (mixedGridOccupiedRow K x) := by
  unfold mixedGridOccupiedRow
  infer_instance

theorem MuThreeMixedGridCode.card_occupiedColumn_eq_six
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (y : Y) :
    Fintype.card (mixedGridOccupiedColumn K y) = 6 := by
  change Fintype.card {u : muThreeMixedCell K // u.1.2 = y} = 6
  rw [Fintype.card_subtype]
  exact code.occupied_column_card_eq_six H K C y

theorem MuThreeMixedGridCode.card_occupiedRow_eq_six
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (x : X) :
    Fintype.card (mixedGridOccupiedRow K x) = 6 := by
  change Fintype.card {u : muThreeMixedCell K // u.1.1 = x} = 6
  rw [Fintype.card_subtype]
  exact code.occupied_row_card_eq_six H K C x

/-- Route every occupied source in column `y` into an `H`-allowed row `x`. -/
noncomputable def mixedGridForeignFiberMap
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (x : X) (y : Y) (hxy : ¬ H x y) :
    mixedGridOccupiedColumn K y → mixedGridOccupiedRow K x := fun u =>
  ⟨mixedGridRowRoute H K C code u.1 x (by simpa [u.2] using hxy),
    mixedGridRowRoute_row H K C code u.1 x (by simpa [u.2] using hxy)⟩

theorem mixedGridForeignFiberMap_injective
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (x : X) (y : Y) (hxy : ¬ H x y) :
    Function.Injective (mixedGridForeignFiberMap H K C code x y hxy) := by
  intro u v huv
  apply Subtype.ext
  by_contra huv'
  have hcolumn : u.1.1.2 = v.1.1.2 := u.2.trans v.2.symm
  have hroute_ne := mixedGridRowRoute_ne_of_sameColumn H K C code
    u.1 v.1 huv' hcolumn x (by simpa [u.2] using hxy)
      (by simpa [v.2] using hxy)
  exact hroute_ne (congrArg Subtype.val huv)

/-- **Foreign-fiber bijection.** For every `H`-allowed `(x,y)`, the exterior
routes give a canonical equivalence from occupied column `y` onto occupied
row `x`. -/
noncomputable def mixedGridForeignFiberEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (x : X) (y : Y) (hxy : ¬ H x y) :
    mixedGridOccupiedColumn K y ≃ mixedGridOccupiedRow K x := by
  refine Equiv.ofBijective (mixedGridForeignFiberMap H K C code x y hxy) ?_
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨mixedGridForeignFiberMap_injective H K C code x y hxy,
    (code.card_occupiedColumn_eq_six H K C y).trans
      (code.card_occupiedRow_eq_six H K C x).symm⟩

theorem mixedGridForeignFiberEquiv_apply
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (x : X) (y : Y) (hxy : ¬ H x y)
    (u : mixedGridOccupiedColumn K y) :
    (mixedGridForeignFiberEquiv H K C code x y hxy u).1 =
      mixedGridRowRoute H K C code u.1 x (by simpa [u.2] using hxy) := rfl

end


end Erdos85

#print axioms Erdos85.mixedGridForeignFiberEquiv
#print axioms Erdos85.mixedGridForeignFiberEquiv_apply
