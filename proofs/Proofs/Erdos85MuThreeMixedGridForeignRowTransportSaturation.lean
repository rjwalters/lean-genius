import Proofs.Erdos85MuThreeMixedGridForeignRowTransportEmbedding

/-!
# Saturated row transport for twin H-columns

When two distinct columns have identical H-neighborhoods, all six rows in
their common H-complement are eligible.  The simultaneous transport
embedding therefore has six-element source and target and is an equivalence:
for every source cell, the six row transports exhaust the target column.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

instance commonForeignRowsFintype
    {X Y : Type*} [Fintype X] (H : X → Y → Prop) [DecidableRel H]
    (b b' : Y) : Fintype (commonForeignRows H b b') := by
  unfold commonForeignRows
  infer_instance

/-- Coordinates identify an occupied column fiber with the K-complement in
that column. -/
noncomputable def occupiedColumnCoordinateEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (K : X → Y → Prop) [DecidableRel K] (b : Y) :
    {u : muThreeMixedCell K // u.1.2 = b} ≃ {x : X // ¬ K x b} where
  toFun u := ⟨u.1.1.1, by simpa [u.2] using u.1.2⟩
  invFun x := ⟨⟨(x.1, b), x.2⟩, rfl⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;> simp [u.2]
  right_inv x := by
    apply Subtype.ext
    rfl

/-- Every occupied column fiber has six cells. -/
theorem MuThreeMixedGridCode.card_occupiedColumnFiber_eq_six
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (b : Y) :
    Fintype.card {u : muThreeMixedCell K // u.1.2 = b} = 6 := by
  rw [Fintype.card_congr (occupiedColumnCoordinateEquiv K b),
    Fintype.card_subtype]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset X)) (p := fun x => K x b)
  simp only [Finset.card_univ, code.card_left] at hpartition
  rw [code.K_twoRegular.2 b] at hpartition
  omega

/-- Twin H-columns have six common eligible rows. -/
theorem MuThreeMixedGridCode.card_commonForeignRows_eq_six_of_twin
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) {b b' : Y}
    (htwin : ∀ x, H x b ↔ H x b') :
    Fintype.card (commonForeignRows H b b') = 6 := by
  classical
  change Fintype.card {x : X // ¬ H x b ∧ ¬ H x b'} = 6
  rw [Fintype.card_subtype]
  have hfilter :
      (Finset.univ.filter fun x : X => ¬ H x b ∧ ¬ H x b') =
        Finset.univ.filter fun x : X => ¬ H x b := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.1
    · intro h
      exact ⟨h, fun hb' => h ((htwin x).mpr hb')⟩
  rw [hfilter]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset X)) (p := fun x => H x b)
  simp only [Finset.card_univ, code.card_left] at hpartition
  rw [code.H_twoRegular.2 b] at hpartition
  omega

/-- In the twin-column regime, row transports at any source cell exhaust the
entire target column fiber. -/
noncomputable def MuThreeMixedGridCode.foreignRowTransportSaturationEquiv
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    {b b' : Y} (hbb' : b ≠ b') (htwin : ∀ x, H x b ↔ H x b')
    (u : {u : muThreeMixedCell K // u.1.2 = b}) :
    commonForeignRows H b b' ≃ {w : muThreeMixedCell K // w.1.2 = b'} := by
  classical
  let f := code.foreignRowTransportOutputEmbedding H K C hbb' u
  exact Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).2
    ⟨f.injective, by
      rw [code.card_commonForeignRows_eq_six_of_twin H K C htwin,
        code.card_occupiedColumnFiber_eq_six H K C b']⟩)

end


end Erdos85

#print axioms Erdos85.occupiedColumnCoordinateEquiv
#print axioms
  Erdos85.MuThreeMixedGridCode.card_occupiedColumnFiber_eq_six
#print axioms
  Erdos85.MuThreeMixedGridCode.card_commonForeignRows_eq_six_of_twin
#print axioms
  Erdos85.MuThreeMixedGridCode.foreignRowTransportSaturationEquiv
