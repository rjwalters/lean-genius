import Proofs.Erdos85MuThreeMixedGridCode
import Proofs.Erdos85SixteenVertexC4CutBound

/-!
# The H-sector sends at least 26 incidences into the partner sector

In the all-triangle mixed grid, disjointness of the two factors makes all
sixteen `H`-edges occupied cells.  The exterior graph is six-regular and
C4-free, so the induced H-sector edge bound forces at least 26 ordered
incidences from H-cells to non-H cells.
-/

open SimpleGraph

namespace Erdos85

/-- The set of occupied cells whose coordinates form an `H`-edge. -/
def mixedGridHCellSet
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) : Set (muThreeMixedCell K) :=
  {u | H u.1.1 u.1.2}

instance mixedGridHCellSetDecidablePred
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] :
    DecidablePred (· ∈ mixedGridHCellSet H K) := by
  unfold mixedGridHCellSet
  infer_instance

/-- Under `H ∩ K = ∅`, the H-cell subtype has cardinality sixteen. -/
theorem MuThreeMixedGridCode.card_mixedGridHCellSet_eq_sixteen
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hdisjoint : ∀ x y, H x y → ¬ K x y) :
    Fintype.card (mixedGridHCellSet H K) = 16 := by
  classical
  rw [Fintype.card_subtype]
  let S := (Finset.univ : Finset (muThreeMixedCell K)).filter
    fun u => H u.1.1 u.1.2
  change S.card = 16
  have hmaps : ∀ u ∈ S, u.1.1 ∈ (Finset.univ : Finset X) := by
    intro u _hu
    exact Finset.mem_univ _
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    ∑ x : X, ((S.filter fun u => u.1.1 = x).card) = ∑ _x : X, 2 := by
      apply Finset.sum_congr rfl
      intro x _hx
      let T := (Finset.univ : Finset Y).filter fun y => H x y
      have hST : (S.filter fun u => u.1.1 = x).card = T.card := by
        apply Finset.card_bij (fun u _hu => u.1.2)
        · intro u hu
          have huS := Finset.mem_filter.mp hu
          have huH := (Finset.mem_filter.mp huS.1).2
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, by simpa [huS.2] using huH⟩
        · intro u hu v hv heq
          apply Subtype.ext
          apply Prod.ext
          · exact (Finset.mem_filter.mp hu).2.trans
              (Finset.mem_filter.mp hv).2.symm
          · exact heq
        · intro y hy
          have hyH : H x y := (Finset.mem_filter.mp hy).2
          let u : muThreeMixedCell K := ⟨(x, y), hdisjoint x y hyH⟩
          refine ⟨u, ?_, rfl⟩
          exact Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hyH⟩, rfl⟩
      rw [hST]
      exact code.H_twoRegular.1 x
    _ = 16 := by simp [code.card_left]

/-- Restriction of the exterior graph to the H-sector remains C4-free. -/
theorem MuThreeMixedGridCode.not_containsC4_induce_mixedGridHCellSet
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C) :
    ¬ containsC4 (mixedGridHCellSet H K) (C.induce (mixedGridHCellSet H K)) := by
  rintro ⟨f, hf, hadj⟩
  apply code.c4Free
  exact ⟨fun i ↦ (f i).1, Subtype.val_injective.comp hf,
    fun i j hij ↦ hadj i j hij⟩

/-- **H-to-partner incidence lower bound.**  At least 26 ordered exterior
edge incidences leave the sixteen H-cells. -/
theorem MuThreeMixedGridCode.twentySix_le_HCell_cutIncidenceCount
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hdisjoint : ∀ x y, H x y → ¬ K x y) :
    26 ≤ graphCutIncidenceCount C (mixedGridHCellSet H K) := by
  apply twentySix_le_graphCutIncidenceCount_of_sixRegular_card_sixteen
    C (mixedGridHCellSet H K)
  · exact code.card_mixedGridHCellSet_eq_sixteen H K C hdisjoint
  · exact code.degree_eq_six H K C
  · exact code.not_containsC4_induce_mixedGridHCellSet H K C

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.card_mixedGridHCellSet_eq_sixteen
#print axioms
  Erdos85.MuThreeMixedGridCode.not_containsC4_induce_mixedGridHCellSet
#print axioms
  Erdos85.MuThreeMixedGridCode.twentySix_le_HCell_cutIncidenceCount
