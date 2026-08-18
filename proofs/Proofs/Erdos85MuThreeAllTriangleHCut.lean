import Proofs.Erdos85MuThreeMixedGridSquarePartition
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

/-- **A forced H-rooted routing fragment.**  Some H-cell has two distinct
exterior neighbours outside the H-sector.  Those neighbours lie in different
rows and different columns. -/
theorem MuThreeMixedGridCode.exists_HCell_two_cross_nonrook_neighbors
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hdisjoint : ∀ x y, H x y → ¬ K x y) :
    ∃ h : mixedGridHCellSet H K, ∃ x y : muThreeMixedCell K,
      x ∈ C.neighborFinset h.1 \ (mixedGridHCellSet H K).toFinset ∧
      y ∈ C.neighborFinset h.1 \ (mixedGridHCellSet H K).toFinset ∧
      x ≠ y ∧ ¬ (mixedGridRowColumnGraph K).Adj x y := by
  classical
  have hcut := code.twentySix_le_HCell_cutIncidenceCount H K C hdisjoint
  have hcard := code.card_mixedGridHCellSet_eq_sixteen H K C hdisjoint
  have hex : ∃ h : mixedGridHCellSet H K,
      1 < (C.neighborFinset h.1 \ (mixedGridHCellSet H K).toFinset).card := by
    by_contra hnone
    push Not at hnone
    have hsum : graphCutIncidenceCount C (mixedGridHCellSet H K) ≤ 16 := by
      rw [graphCutIncidenceCount]
      calc
        ∑ h : mixedGridHCellSet H K,
            (C.neighborFinset h.1 \ (mixedGridHCellSet H K).toFinset).card ≤
            ∑ _h : mixedGridHCellSet H K, 1 := by
          apply Finset.sum_le_sum
          intro h _hh
          exact hnone h
        _ = 16 := by simp [hcard]
    omega
  obtain ⟨h, hh⟩ := hex
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hh
  refine ⟨h, x, y, hx, hy, hxy, ?_⟩
  intro hrook
  have hhx : C.Adj h.1 x :=
    (C.mem_neighborFinset h.1 x).mp (Finset.mem_sdiff.mp hx).1
  have hhy : C.Adj h.1 y :=
    (C.mem_neighborFinset h.1 y).mp (Finset.mem_sdiff.mp hy).1
  have hsep := code.rook h.1 x y hhx hhy hxy
  exact hrook.2.elim hsep.1 hsep.2

/-- **Two distinct rich H-roots.**  At least two H-cells have two or more
neighbours across the H/non-H cut.  Indeed, if only one root were rich, its
degree-six cap and the fifteen remaining degree-one caps would total at most
`6 + 15 = 21`, below the forced cut size 26. -/
theorem MuThreeMixedGridCode.exists_two_HCells_with_two_cross_neighbors
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    (H K : X → Y → Prop) [DecidableRel H] [DecidableRel K]
    (C : SimpleGraph (muThreeMixedCell K)) [DecidableRel C.Adj]
    (code : MuThreeMixedGridCode H K C)
    (hdisjoint : ∀ x y, H x y → ¬ K x y) :
    ∃ h₁ h₂ : mixedGridHCellSet H K, h₁ ≠ h₂ ∧
      1 < (C.neighborFinset h₁.1 \ (mixedGridHCellSet H K).toFinset).card ∧
      1 < (C.neighborFinset h₂.1 \ (mixedGridHCellSet H K).toFinset).card := by
  classical
  let cutDegree := fun h : mixedGridHCellSet H K =>
    (C.neighborFinset h.1 \ (mixedGridHCellSet H K).toFinset).card
  have hcut : 26 ≤ ∑ h : mixedGridHCellSet H K, cutDegree h := by
    simpa [graphCutIncidenceCount, cutDegree] using
      code.twentySix_le_HCell_cutIncidenceCount H K C hdisjoint
  have hcard := code.card_mixedGridHCellSet_eq_sixteen H K C hdisjoint
  have hex₁ : ∃ h : mixedGridHCellSet H K, 1 < cutDegree h := by
    by_contra hnone
    push Not at hnone
    have hsum : (∑ h : mixedGridHCellSet H K, cutDegree h) ≤ 16 := by
      calc
        ∑ h : mixedGridHCellSet H K, cutDegree h ≤
            ∑ _h : mixedGridHCellSet H K, 1 := by
          apply Finset.sum_le_sum
          intro h _hh
          exact hnone h
        _ = 16 := by simp [hcard]
    omega
  obtain ⟨h₁, hh₁⟩ := hex₁
  by_cases hex₂ : ∃ h₂ : mixedGridHCellSet H K, h₁ ≠ h₂ ∧ 1 < cutDegree h₂
  · obtain ⟨h₂, hh₂, hrich₂⟩ := hex₂
    exact ⟨h₁, h₂, hh₂, hh₁, hrich₂⟩
  · push Not at hex₂
    have hcap₁ : cutDegree h₁ ≤ 6 := by
      calc
        cutDegree h₁ ≤ (C.neighborFinset h₁.1).card :=
          Finset.card_le_card (Finset.sdiff_subset)
        _ = C.degree h₁.1 := C.card_neighborFinset_eq_degree h₁.1
        _ = 6 := code.degree_eq_six H K C h₁.1
    have hsum : (∑ h : mixedGridHCellSet H K, cutDegree h) ≤ 21 := by
      calc
        ∑ h : mixedGridHCellSet H K, cutDegree h ≤
            ∑ h : mixedGridHCellSet H K, if h = h₁ then 6 else 1 := by
          apply Finset.sum_le_sum
          intro h _hh
          by_cases heq : h = h₁
          · simpa [heq] using hcap₁
          · rw [if_neg heq]
            exact hex₂ h (Ne.symm heq)
        _ = ∑ h : mixedGridHCellSet H K,
              (1 + if h = h₁ then 5 else 0) := by
          apply Finset.sum_congr rfl
          intro h _hh
          split <;> omega
        _ = 21 := by
          rw [Finset.sum_add_distrib]
          have hones : (∑ _h : mixedGridHCellSet H K, 1) = 16 := by
            simp [hcard]
          have hfive :
              (∑ h : mixedGridHCellSet H K, if h = h₁ then 5 else 0) = 5 := by
            simp
          rw [hones, hfive]
    omega

end Erdos85

#print axioms Erdos85.MuThreeMixedGridCode.card_mixedGridHCellSet_eq_sixteen
#print axioms
  Erdos85.MuThreeMixedGridCode.not_containsC4_induce_mixedGridHCellSet
#print axioms
  Erdos85.MuThreeMixedGridCode.twentySix_le_HCell_cutIncidenceCount
#print axioms
  Erdos85.MuThreeMixedGridCode.exists_HCell_two_cross_nonrook_neighbors
#print axioms
  Erdos85.MuThreeMixedGridCode.exists_two_HCells_with_two_cross_neighbors
