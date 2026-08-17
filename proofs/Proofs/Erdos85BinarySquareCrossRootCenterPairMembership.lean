import Proofs.Erdos85BinarySquareCrossRootCenterPairs

/-! # Common-neighbor characterization of cross-root transition edges -/

open SimpleGraph

namespace Erdos85

noncomputable section

/-- Inside the ambient center grid, a pair belongs to the transition graph
contributed by a remote target component exactly when its two coordinates
have a common neighbor in that target. -/
theorem mem_crossRootCenterPairFinset_iff_exists_commonNeighbor_in_target
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d e : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (x y : d.supp) (p : V × V)
    (hpgrid : p ∈ crossRootCenterGrid G x.1 y.1) :
    p ∈ crossRootCenterPairFinset G hfree hde x y ↔
      ∃ w : e.supp, G.Adj p.1 w.1 ∧ G.Adj p.2 w.1 := by
  classical
  have hpgrid' := Finset.mem_product.mp hpgrid
  have hxp : G.Adj x.1 p.1 := (G.mem_neighborFinset x.1 p.1).mp hpgrid'.1
  have hyp : G.Adj y.1 p.2 := (G.mem_neighborFinset y.1 p.2).mp hpgrid'.2
  constructor
  · intro hp
    obtain ⟨w, _hw, hpEq⟩ := Finset.mem_image.mp hp
    refine ⟨w, ?_, ?_⟩
    · rw [← congrArg Prod.fst hpEq]
      exact (crossCommonNeighbor_spec G hfree hde x w).2.symm
    · rw [← congrArg Prod.snd hpEq]
      exact (crossCommonNeighbor_spec G hfree hde y w).2.symm
  · rintro ⟨w, hpw, hqw⟩
    apply Finset.mem_image.mpr
    refine ⟨w, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · exact (eq_crossCommonNeighbor_of_adj G hfree hde x w
        ⟨hxp, hpw.symm⟩).symm
    · exact (eq_crossCommonNeighbor_of_adj G hfree hde y w
        ⟨hyp, hqw.symm⟩).symm

/-- Consequently the complement of the union of several remote transition
graphs consists exactly of center pairs having no common neighbor in any of
those target components. -/
theorem mem_centerGrid_sdiff_three_crossRootCenterPairFinsets_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 V G)
    {d e f g : (secondOrderDefectGraph G).ConnectedComponent}
    (hde : d ≠ e) (hdf : d ≠ f) (hdg : d ≠ g)
    (x y : d.supp) (p : V × V) :
    p ∈ crossRootCenterGrid G x.1 y.1 \ ((
        crossRootCenterPairFinset G hfree hde x y ∪
          crossRootCenterPairFinset G hfree hdf x y) ∪
        crossRootCenterPairFinset G hfree hdg x y) ↔
      p ∈ crossRootCenterGrid G x.1 y.1 ∧
        (¬ ∃ w : e.supp, G.Adj p.1 w.1 ∧ G.Adj p.2 w.1) ∧
        (¬ ∃ w : f.supp, G.Adj p.1 w.1 ∧ G.Adj p.2 w.1) ∧
        (¬ ∃ w : g.supp, G.Adj p.1 w.1 ∧ G.Adj p.2 w.1) := by
  classical
  constructor
  · intro hp
    have hp' := Finset.mem_sdiff.mp hp
    have hnot := hp'.2
    simp only [Finset.mem_union, not_or] at hnot
    refine ⟨hp'.1, ?_, ?_, ?_⟩
    · simpa [mem_crossRootCenterPairFinset_iff_exists_commonNeighbor_in_target
        G hfree hde x y p hp'.1] using hnot.1.1
    · simpa [mem_crossRootCenterPairFinset_iff_exists_commonNeighbor_in_target
        G hfree hdf x y p hp'.1] using hnot.1.2
    · simpa [mem_crossRootCenterPairFinset_iff_exists_commonNeighbor_in_target
        G hfree hdg x y p hp'.1] using hnot.2
  · rintro ⟨hpgrid, he, hf, hg⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨hpgrid, ?_⟩
    simp only [Finset.mem_union, not_or]
    exact ⟨⟨
      (mem_crossRootCenterPairFinset_iff_exists_commonNeighbor_in_target
        G hfree hde x y p hpgrid).not.mpr he,
      (mem_crossRootCenterPairFinset_iff_exists_commonNeighbor_in_target
        G hfree hdf x y p hpgrid).not.mpr hf⟩,
      (mem_crossRootCenterPairFinset_iff_exists_commonNeighbor_in_target
        G hfree hdg x y p hpgrid).not.mpr hg⟩

end

end Erdos85
