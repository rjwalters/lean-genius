import Proofs.Erdos85MuThreeMixedGridCode

/-!
# Twin-row obstruction in the all-triangle-free `mu = 3` grid

When the forbidden factor is the ambient factor (`K = H`), two distinct
rows cannot have the same two `H`-neighbours.  Indeed, the 36 occupied cells
whose columns avoid those two neighbours each determine a pair of exterior
neighbours, one in either row.  The rook law puts these pairs among the 30
different-column pairs, while C4-freeness makes the assignment injective.

This uniformly excludes every factor stratum containing a four-cycle; it is
not an enumeration of the order-eight instances.
-/

open SimpleGraph

namespace Erdos85

section

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  (H : X → Y → Prop) [DecidableRel H]
  (C : SimpleGraph (muThreeMixedCell H)) [DecidableRel C.Adj]

/-- Occupied cells in a fixed row. -/
def muThreeMixedRow (x : X) : Finset (muThreeMixedCell H) :=
  Finset.univ.filter fun u => u.1.1 = x

/-- Occupied cells whose column is not incident with `x` in `H`. -/
def muThreeMixedEligibleCenters (x : X) : Finset (muThreeMixedCell H) :=
  Finset.univ.filter fun u => ¬ H x u.1.2

/-- Ordered pairs in two prescribed rows and in different columns. -/
def muThreeMixedCrossRowPairs (x x' : X) :
    Finset (muThreeMixedCell H × muThreeMixedCell H) :=
  Finset.univ.filter fun p =>
    p.1.1.1 = x ∧ p.2.1.1 = x' ∧ p.1.1.2 ≠ p.2.1.2

theorem MuThreeMixedGridCode.card_row_eq_six
    (code : MuThreeMixedGridCode H H C) (x : X) :
    (muThreeMixedRow H x).card = 6 := by
  classical
  let e : (↥(muThreeMixedRow H x)) ≃ {y : Y // ¬ H x y} := {
    toFun := fun u => ⟨u.1.1.2, by
      have hx : u.1.1.1 = x := (Finset.mem_filter.mp u.2).2
      simpa [hx] using u.1.2⟩
    invFun := fun y => ⟨⟨(x, y.1), y.2⟩, by simp [muThreeMixedRow]⟩
    left_inv u := by
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext (Finset.mem_filter.mp u.2).2.symm rfl
    right_inv y := by simp }
  have hcard : Fintype.card {y : Y // ¬ H x y} = 6 := by
    rw [Fintype.card_subtype]
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset Y)) (p := fun y => H x y)
    have htwo := code.H_twoRegular.1 x
    simp only [Finset.card_univ, code.card_right] at hpart
    rw [htwo] at hpart
    omega
  calc
    (muThreeMixedRow H x).card = Fintype.card (↥(muThreeMixedRow H x)) := by
      simp
    _ = Fintype.card {y : Y // ¬ H x y} := Fintype.card_congr e
    _ = 6 := hcard

/-- There are `6 * 6 = 36` occupied centers whose column avoids a fixed row
of the two-factor. -/
theorem MuThreeMixedGridCode.card_eligibleCenters_eq_thirtySix
    (code : MuThreeMixedGridCode H H C) (x : X) :
    (muThreeMixedEligibleCenters H x).card = 36 := by
  classical
  let e : (↥(muThreeMixedEligibleCenters H x)) ≃
      (Σ y : {y : Y // ¬ H x y}, {z : X // ¬ H z y.1}) := {
    toFun := fun u => ⟨⟨u.1.1.2, (Finset.mem_filter.mp u.2).2⟩,
      ⟨u.1.1.1, u.1.2⟩⟩
    invFun := fun p => ⟨⟨(p.2.1, p.1.1), p.2.2⟩, by
      simp [muThreeMixedEligibleCenters, p.1.2]⟩
    left_inv := by intro u; rfl
    right_inv := by intro p; cases p with | mk y z => cases y; cases z; rfl }
  have hA : Fintype.card {y : Y // ¬ H x y} = 6 := by
    rw [Fintype.card_subtype]
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset Y)) (p := fun y => H x y)
    have htwo := code.H_twoRegular.1 x
    simp only [Finset.card_univ, code.card_right] at hpart
    rw [htwo] at hpart
    omega
  have hB : ∀ y : {y : Y // ¬ H x y},
      Fintype.card {z : X // ¬ H z y.1} = 6 := by
    intro y
    rw [Fintype.card_subtype]
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset X)) (p := fun z => H z y.1)
    have htwo := code.H_twoRegular.2 y.1
    simp only [Finset.card_univ, code.card_left] at hpart
    rw [htwo] at hpart
    omega
  calc
    (muThreeMixedEligibleCenters H x).card =
        Fintype.card (↥(muThreeMixedEligibleCenters H x)) := by simp
    _ = Fintype.card (Σ y : {y : Y // ¬ H x y},
        {z : X // ¬ H z y.1}) := Fintype.card_congr e
    _ = ∑ y : {y : Y // ¬ H x y},
        Fintype.card {z : X // ¬ H z y.1} := Fintype.card_sigma
    _ = 6 * 6 := by simp_rw [hB]; simp [hA]
    _ = 36 := by norm_num

/-- Twin rows have exactly `6 * 5 = 30` ordered different-column pairs. -/
theorem MuThreeMixedGridCode.card_crossRowPairs_eq_thirty
    (code : MuThreeMixedGridCode H H C) {x x' : X}
    (htwin : ∀ y, H x y ↔ H x' y) :
    (muThreeMixedCrossRowPairs H x x').card = 30 := by
  classical
  let A := {y : Y // ¬ H x y}
  let e : (↥(muThreeMixedCrossRowPairs H x x')) ≃
      (Σ y : A, {z : A // z ≠ y}) := {
    toFun := fun p =>
      ⟨⟨p.1.1.1.2, by
          have hx : p.1.1.1.1 = x := (Finset.mem_filter.mp p.2).2.1
          simpa [hx] using p.1.1.2⟩,
        ⟨⟨p.1.2.1.2, by
            have hx' : p.1.2.1.1 = x' := (Finset.mem_filter.mp p.2).2.2.1
            have hn : ¬ H x' p.1.2.1.2 := by simpa [hx'] using p.1.2.2
            exact fun h => hn ((htwin _).mp h)⟩,
          by
            intro h
            exact (Finset.mem_filter.mp p.2).2.2.2 (Subtype.ext_iff.mp h).symm⟩⟩
    invFun := fun p =>
      ⟨(⟨(x, p.1.1), p.1.2⟩, ⟨(x', p.2.1.1), by
          exact fun h => p.2.1.2 ((htwin _).mpr h)⟩), by
        simp only [muThreeMixedCrossRowPairs, Finset.mem_filter, Finset.mem_univ,
          true_and]
        intro h
        exact p.2.2 (Subtype.ext h.symm)⟩
    left_inv := by
      intro p
      apply Subtype.ext
      apply Prod.ext <;> apply Subtype.ext
      · exact Prod.ext (Finset.mem_filter.mp p.2).2.1.symm rfl
      · exact Prod.ext (Finset.mem_filter.mp p.2).2.2.1.symm rfl
    right_inv := by
      intro p
      cases p with
      | mk y z => cases y; cases z with | mk z hz => cases z; rfl }
  have hA : Fintype.card A = 6 := by
    rw [Fintype.card_subtype]
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset Y)) (p := fun y => H x y)
    have htwo := code.H_twoRegular.1 x
    simp only [Finset.card_univ, code.card_right] at hpart
    rw [htwo] at hpart
    omega
  have hneq : ∀ y : A, Fintype.card {z : A // z ≠ y} = 5 := by
    intro y
    rw [Fintype.card_subtype_compl (fun z : A => z = y)]
    simp [hA]
  calc
    (muThreeMixedCrossRowPairs H x x').card =
        Fintype.card (↥(muThreeMixedCrossRowPairs H x x')) := by simp
    _ = Fintype.card (Σ y : A, {z : A // z ≠ y}) := Fintype.card_congr e
    _ = ∑ y : A, Fintype.card {z : A // z ≠ y} := Fintype.card_sigma
    _ = 6 * 5 := by simp_rw [hneq]; simp [hA]
    _ = 30 := by norm_num

/-- The unique neighbour of `u` in row `x`, when that row is hit. -/
noncomputable def MuThreeMixedGridCode.rowNeighbor
    (code : MuThreeMixedGridCode H H C) (u : muThreeMixedCell H) (x : X)
    (h : ¬ H x u.1.2) : muThreeMixedCell H :=
  Classical.choose ((code.existsUnique_row_neighbor_iff H H C u x).mpr h)

theorem MuThreeMixedGridCode.rowNeighbor_spec
    (code : MuThreeMixedGridCode H H C) (u : muThreeMixedCell H) (x : X)
    (h : ¬ H x u.1.2) :
    C.Adj u (code.rowNeighbor H C u x h) ∧
      (code.rowNeighbor H C u x h).1.1 = x :=
  Classical.choose_spec ((code.existsUnique_row_neighbor_iff H H C u x).mpr h) |>.1

/-- A C4-free mixed grid with `K = H` has no two distinct twin rows.  This
is the uniform pigeonhole obstruction `36 ≤ 30`. -/
theorem MuThreeMixedGridCode.no_distinct_twin_rows
    (code : MuThreeMixedGridCode H H C) {x x' : X} (hxx' : x ≠ x') :
    ¬ (∀ y, H x y ↔ H x' y) := by
  classical
  intro htwin
  let source := ↥(muThreeMixedEligibleCenters H x)
  let target := ↥(muThreeMixedCrossRowPairs H x x')
  let f : source → target := fun w => by
    have hx : ¬ H x w.1.1.2 := (Finset.mem_filter.mp w.2).2
    have hx' : ¬ H x' w.1.1.2 := fun h => hx ((htwin _).mpr h)
    let a := code.rowNeighbor H C w.1 x hx
    let b := code.rowNeighbor H C w.1 x' hx'
    have ha := code.rowNeighbor_spec H C w.1 x hx
    have hb := code.rowNeighbor_spec H C w.1 x' hx'
    have hab : a ≠ b := by
      intro heq
      apply hxx'
      exact ha.2.symm.trans ((congrArg (fun u : muThreeMixedCell H => u.1.1) heq).trans hb.2)
    have hcol : a.1.2 ≠ b.1.2 := (code.rook w.1 a b ha.1 hb.1 hab).2
    exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha.2, hb.2, hcol⟩⟩
  have hf : Function.Injective f := by
    intro w w' heq
    apply Subtype.ext
    have hp : (f w).1 = (f w').1 := congrArg Subtype.val heq
    have ha : (f w).1.1 = (f w').1.1 := congrArg Prod.fst hp
    have hb : (f w).1.2 = (f w').1.2 := congrArg Prod.snd hp
    have hab : (f w).1.1 ≠ (f w).1.2 := by
      intro h
      have hm := (Finset.mem_filter.mp (f w).2).2
      exact hxx' (hm.1.symm.trans ((congrArg
        (fun u : muThreeMixedCell H => u.1.1) h).trans hm.2.1))
    have hle := code.common_neighbor_card_le_one H H C
      (f w).1.1 (f w).1.2 hab
    apply Finset.card_le_one.mp hle w.1
    · apply Finset.mem_inter.mpr
      constructor
      · apply (C.mem_neighborFinset (f w).1.1 w.1).mpr
        have hx : ¬ H x w.1.1.2 := (Finset.mem_filter.mp w.2).2
        exact (code.rowNeighbor_spec H C w.1 x hx).1.symm
      · apply (C.mem_neighborFinset (f w).1.2 w.1).mpr
        have hx : ¬ H x w.1.1.2 := (Finset.mem_filter.mp w.2).2
        have hx' : ¬ H x' w.1.1.2 := fun h => hx ((htwin _).mpr h)
        exact (code.rowNeighbor_spec H C w.1 x' hx').1.symm
    · apply Finset.mem_inter.mpr
      constructor
      · apply (C.mem_neighborFinset (f w).1.1 w'.1).mpr
        rw [ha]
        have hx : ¬ H x w'.1.1.2 := (Finset.mem_filter.mp w'.2).2
        exact (code.rowNeighbor_spec H C w'.1 x hx).1.symm
      · apply (C.mem_neighborFinset (f w).1.2 w'.1).mpr
        rw [hb]
        have hx : ¬ H x w'.1.1.2 := (Finset.mem_filter.mp w'.2).2
        have hx' : ¬ H x' w'.1.1.2 := fun h => hx ((htwin _).mpr h)
        exact (code.rowNeighbor_spec H C w'.1 x' hx').1.symm
  have hcard := Fintype.card_le_of_injective f hf
  dsimp [source, target] at hcard
  have hcard' : (muThreeMixedEligibleCenters H x).card ≤
      (muThreeMixedCrossRowPairs H x x').card := by
    simpa only [Fintype.card_coe] using hcard
  rw [code.card_eligibleCenters_eq_thirtySix H C x,
    code.card_crossRowPairs_eq_thirty H C htwin] at hcard'
  omega

end

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.card_row_eq_six
#print axioms Erdos85.MuThreeMixedGridCode.card_eligibleCenters_eq_thirtySix
#print axioms Erdos85.MuThreeMixedGridCode.card_crossRowPairs_eq_thirty
#print axioms Erdos85.MuThreeMixedGridCode.no_distinct_twin_rows
