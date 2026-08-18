import Proofs.Erdos85MuThreeMixedGridTwinColumnsFourCycle

/-!
# The saturated twin-column transport table is Latin

For distinct twin H-columns `b,b'`, transport defines a `6 × 6` table:
source cells in column `b` by common eligible rows, valued in column `b'`.
Every fixed-row slice is a matching equivalence, and saturation says every
fixed-source slice is an equivalence.  Hence this table is a Latin square of
order six.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- The saturated transport table between twin columns. -/
noncomputable def MuThreeMixedGridCode.twinColumnTransportTable
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {b b' : Y} (_hbb' : b ≠ b') (_htwin : ∀ x, H x b ↔ H x b')
    (u : {u : muThreeMixedCell K // u.1.2 = b})
    (x : commonForeignRows H b b') :
    {w : muThreeMixedCell K // w.1.2 = b'} :=
  code.foreignRowTransportEquiv H K C x.1 b b' x.2.1 x.2.2 u

/-- Each fixed eligible row gives a bijection between the two column
fibers. -/
theorem MuThreeMixedGridCode.twinColumnTransportTable_bijective_source
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {b b' : Y} (hbb' : b ≠ b') (htwin : ∀ x, H x b ↔ H x b')
    (x : commonForeignRows H b b') :
    Function.Bijective (fun u =>
      code.twinColumnTransportTable H K C hbb' htwin u x) := by
  exact (code.foreignRowTransportEquiv H K C x.1 b b'
    x.2.1 x.2.2).bijective

/-- Each fixed source cell gives a bijection from the six eligible rows to
the target fiber. -/
theorem MuThreeMixedGridCode.twinColumnTransportTable_bijective_row
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {b b' : Y} (hbb' : b ≠ b') (htwin : ∀ x, H x b ↔ H x b')
    (u : {u : muThreeMixedCell K // u.1.2 = b}) :
    Function.Bijective (fun x =>
      code.twinColumnTransportTable H K C hbb' htwin u x) := by
  exact (code.foreignRowTransportSaturationEquiv H K C hbb' htwin u).bijective

/-- Packaged Latin-square law: the transport table is bijective in either
coordinate when the other is fixed. -/
theorem MuThreeMixedGridCode.twinColumnTransportTable_latin
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {b b' : Y} (hbb' : b ≠ b') (htwin : ∀ x, H x b ↔ H x b') :
    (∀ x, Function.Bijective (fun u =>
      code.twinColumnTransportTable H K C hbb' htwin u x)) ∧
      (∀ u, Function.Bijective (fun x =>
        code.twinColumnTransportTable H K C hbb' htwin u x)) := by
  exact ⟨fun x => code.twinColumnTransportTable_bijective_source
    H K C hbb' htwin x,
    fun u => code.twinColumnTransportTable_bijective_row
      H K C hbb' htwin u⟩

end


end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.twinColumnTransportTable
#print axioms
  Erdos85.MuThreeMixedGridCode.twinColumnTransportTable_bijective_source
#print axioms
  Erdos85.MuThreeMixedGridCode.twinColumnTransportTable_bijective_row
#print axioms
  Erdos85.MuThreeMixedGridCode.twinColumnTransportTable_latin
