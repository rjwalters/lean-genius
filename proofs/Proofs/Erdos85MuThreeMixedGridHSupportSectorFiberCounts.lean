import Proofs.Erdos85MuThreeMixedGridHSupportFiberCounts

/-!
# Sector-level occupied H-support fiber counts

Cycle compatibility makes each H-component wholly forbidden (`H ⊆ K`) or
wholly occupied (`H ∩ K = ∅`).  Consequently every row and column fiber has
either zero or exactly two occupied H-cells.  These zero/two subsets are the
distinguished K-sector data carried by the six-point monodromy fibers.
-/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Every column contains either zero or two occupied H-support cells. -/
theorem MuThreeMixedGridCode.HSupport_column_card_eq_zero_or_two
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (b : Y) :
    ((mixedGridHSupport H K).filter fun u => u.1.2 = b).card = 0 ∨
      ((mixedGridHSupport H K).filter fun u => u.1.2 = b).card = 2 := by
  classical
  let c := (relationBipartiteGraph H).connectedComponentMk (Sum.inr b)
  have hbC : Sum.inr b ∈ c.supp :=
    (ConnectedComponent.mem_supp_iff c _).mpr rfl
  rcases code.cycle_compatible c with hall | hnone
  · left
    apply Finset.card_eq_zero.mpr
    ext u
    simp only [Finset.notMem_empty, iff_false]
    intro hu
    have hu' := Finset.mem_filter.mp hu
    have huH := (Finset.mem_filter.mp hu'.1).2
    have huCol := hu'.2
    have huAdj : (relationBipartiteGraph H).Adj
        (Sum.inr b) (Sum.inl u.1.1) := by
      change H u.1.1 b
      simpa [huCol] using huH
    have huC : Sum.inl u.1.1 ∈ c.supp :=
      (ConnectedComponent.mem_supp_congr_adj c huAdj).mp hbC
    exact u.2 (by simpa [huCol] using hall u.1.1 b (by simpa [huCol] using huH) huC)
  · right
    let S := (mixedGridHSupport H K).filter fun u => u.1.2 = b
    let T := (Finset.univ : Finset X).filter fun x => H x b
    have hcard : S.card = T.card := by
      apply Finset.card_bij (fun u _hu => u.1.1)
      · intro u hu
        have hu' := Finset.mem_filter.mp hu
        have huH := (Finset.mem_filter.mp hu'.1).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hu'.2] using huH⟩
      · intro u hu v hv huv
        apply Subtype.ext
        apply Prod.ext
        · exact huv
        · exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
      · intro x hx
        have hxH := (Finset.mem_filter.mp hx).2
        have hxAdj : (relationBipartiteGraph H).Adj
            (Sum.inr b) (Sum.inl x) := hxH
        have hxC : Sum.inl x ∈ c.supp :=
          (ConnectedComponent.mem_supp_congr_adj c hxAdj).mp hbC
        have hxK : ¬ K x b := hnone x b hxH hxC
        let u : muThreeMixedCell K := ⟨(x, b), hxK⟩
        refine ⟨u, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hxH⟩, rfl⟩
    change S.card = 2
    rw [hcard]
    exact code.H_twoRegular.2 b

/-- Every row contains either zero or two occupied H-support cells. -/
theorem MuThreeMixedGridCode.HSupport_row_card_eq_zero_or_two
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) (a : X) :
    ((mixedGridHSupport H K).filter fun u => u.1.1 = a).card = 0 ∨
      ((mixedGridHSupport H K).filter fun u => u.1.1 = a).card = 2 := by
  classical
  let c := (relationBipartiteGraph H).connectedComponentMk (Sum.inl a)
  have haC : Sum.inl a ∈ c.supp :=
    (ConnectedComponent.mem_supp_iff c _).mpr rfl
  rcases code.cycle_compatible c with hall | hnone
  · left
    apply Finset.card_eq_zero.mpr
    ext u
    simp only [Finset.notMem_empty, iff_false]
    intro hu
    have hu' := Finset.mem_filter.mp hu
    have huH := (Finset.mem_filter.mp hu'.1).2
    have huRow := hu'.2
    exact u.2 (by
      simpa [huRow] using hall a u.1.2 (by simpa [huRow] using huH) haC)
  · right
    let S := (mixedGridHSupport H K).filter fun u => u.1.1 = a
    let T := (Finset.univ : Finset Y).filter fun y => H a y
    have hcard : S.card = T.card := by
      apply Finset.card_bij (fun u _hu => u.1.2)
      · intro u hu
        have hu' := Finset.mem_filter.mp hu
        have huH := (Finset.mem_filter.mp hu'.1).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hu'.2] using huH⟩
      · intro u hu v hv huv
        apply Subtype.ext
        apply Prod.ext
        · exact (Finset.mem_filter.mp hu).2.trans (Finset.mem_filter.mp hv).2.symm
        · exact huv
      · intro y hy
        have hyH := (Finset.mem_filter.mp hy).2
        have hyK : ¬ K a y := hnone a y hyH haC
        let u : muThreeMixedCell K := ⟨(a, y), hyK⟩
        refine ⟨u, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hyH⟩, rfl⟩
    change S.card = 2
    rw [hcard]
    exact code.H_twoRegular.1 a

end

end Erdos85

#print axioms
  Erdos85.MuThreeMixedGridCode.HSupport_column_card_eq_zero_or_two
#print axioms
  Erdos85.MuThreeMixedGridCode.HSupport_row_card_eq_zero_or_two
