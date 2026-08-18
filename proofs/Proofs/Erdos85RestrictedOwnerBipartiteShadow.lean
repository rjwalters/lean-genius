import Proofs.Erdos85BipartiteTwoRegularHall
import Proofs.Erdos85BinarySquareSizeTwoCrossBlockNoRectangle

/-! # Restricted owner factors are the two shores of a cross-block shadow -/

open SimpleGraph

namespace Erdos85

noncomputable section

theorem BipartiteTwoRegularAfterMatching.rel_iff_matching_or_residual
    {S T : Type*} {R : S → T → Prop} {f : S ≃ T}
    (h : BipartiteTwoRegularAfterMatching R f) (s : S) (t : T) :
    R s t ↔ t = f s ∨ t = h.residualEquiv s := by
  constructor
  · intro hst
    by_cases htf : t = f s
    · exact Or.inl htf
    · right
      symm
      exact (h.residual_unique_left s).unique
        (h.residual_unique_left s).choose_spec.1 ⟨hst, htf⟩
  · rintro (rfl | rfl)
    · exact h.matching_mem s
    · exact (h.residualEquiv_mem s).1

theorem BipartiteTwoRegularAfterMatching.left_common_iff_shadow
    {S T : Type*} {R : S → T → Prop} {f : S ≃ T}
    (h : BipartiteTwoRegularAfterMatching R f) {x y : S} (hxy : x ≠ y) :
    (∃ t, R x t ∧ R y t) ↔
      bipartiteLeftShadow f h.residualEquiv x = y ∨
        bipartiteLeftShadow f h.residualEquiv y = x := by
  constructor
  · rintro ⟨t, hxt, hyt⟩
    rw [h.rel_iff_matching_or_residual] at hxt hyt
    rcases hxt with rfl | rfl <;> rcases hyt with hy | hy
    · exact (hxy (f.injective hy)).elim
    · right
      change f.symm (h.residualEquiv y) = x
      rw [← hy, f.symm_apply_apply]
    · left
      change f.symm (h.residualEquiv x) = y
      rw [hy, f.symm_apply_apply]
    · exact (hxy (h.residualEquiv.injective hy)).elim
  · rintro (hshadow | hshadow)
    · refine ⟨h.residualEquiv x, (h.residualEquiv_mem x).1, ?_⟩
      have heq : h.residualEquiv x = f y := by
        apply f.symm.injective
        simpa [bipartiteLeftShadow] using hshadow
      rw [heq]
      exact h.matching_mem y
    · refine ⟨h.residualEquiv y, ?_, (h.residualEquiv_mem y).1⟩
      have heq : h.residualEquiv y = f x := by
        apply f.symm.injective
        simpa [bipartiteLeftShadow] using hshadow
      rw [heq]
      exact h.matching_mem x

theorem BipartiteTwoRegularAfterMatching.right_common_iff_shadow
    {S T : Type*} {R : S → T → Prop} {f : S ≃ T}
    (h : BipartiteTwoRegularAfterMatching R f) {x y : T} (hxy : x ≠ y) :
    (∃ s, R s x ∧ R s y) ↔
      bipartiteRightShadow f h.residualEquiv x = y ∨
        bipartiteRightShadow f h.residualEquiv y = x := by
  constructor
  · rintro ⟨s, hsx, hsy⟩
    rw [h.rel_iff_matching_or_residual] at hsx hsy
    rcases hsx with hx | hx <;> rcases hsy with hy | hy
    · exact (hxy (hx.trans hy.symm)).elim
    · left
      change h.residualEquiv (f.symm x) = y
      rw [hx, f.symm_apply_apply, ← hy]
    · right
      change h.residualEquiv (f.symm y) = x
      rw [hy, f.symm_apply_apply, ← hx]
    · exact (hxy (hx.trans hy.symm)).elim
  · rintro (hshadow | hshadow)
    · refine ⟨f.symm x, ?_, ?_⟩
      · simpa using h.matching_mem (f.symm x)
      · rw [h.rel_iff_matching_or_residual]
        exact Or.inr hshadow.symm
    · refine ⟨f.symm y, ?_, ?_⟩
      · rw [h.rel_iff_matching_or_residual]
        exact Or.inr hshadow.symm
      · simpa using h.matching_mem (f.symm y)

/-- A normalized size-two cross block admits matching coordinates in which
the restricted owner graph on each shore is exactly the undirected shadow
of the two matching permutations. -/
theorem binarySquare_regular_twoSizeTwoParts_restrictedOwners_are_shadows
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    [Fintype (secondOrderDefectGraph G).ConnectedComponent]
    [DecidableEq (secondOrderDefectGraph G).ConnectedComponent]
    (hfree : ¬ containsC4 V G) {q : ℕ} (hq : 3 ≤ q)
    (hreg : ∀ x, G.degree x = q)
    (hcard : Fintype.card V = q * q)
    (source target : (secondOrderDefectGraph G).ConnectedComponent)
    (hsource : source.supp.ncard = q * 2)
    (htarget : target.supp.ncard = q * 2) :
    ∃ (f : source.supp ≃ target.supp)
      (h : BipartiteTwoRegularAfterMatching
        (fun x y => G.Adj x.1 y.1) f),
      (∀ x y,
        (restrictedComponentOwnerGraph G source target).Adj x y ↔
          x ≠ y ∧
            (bipartiteLeftShadow f h.residualEquiv x = y ∨
             bipartiteLeftShadow f h.residualEquiv y = x)) ∧
      (∀ x y,
        (restrictedComponentOwnerGraph G target source).Adj x y ↔
          x ≠ y ∧
            (bipartiteRightShadow f h.residualEquiv x = y ∨
             bipartiteRightShadow f h.residualEquiv y = x)) := by
  have hpkg := binarySquare_regular_twoSizeTwoParts_crossIndexedBlock_package
    G hfree hq hreg hcard source target hsource htarget
  let R : source.supp → target.supp → Prop := fun x y => G.Adj x.1 y.1
  have hS : ∀ x, (Finset.univ.filter (R x)).card = 2 := hpkg.2.1
  have hT : ∀ y, (Finset.univ.filter (fun x => R x y)).card = 2 := by
    intro y
    simpa [R, componentCrossNeighborFinset, G.adj_comm] using hpkg.2.2 y
  obtain ⟨f, h⟩ := twoRegularBipartite_exists_afterMatching R hS hT
  refine ⟨f, h, ?_, ?_⟩
  · intro x y
    rw [restrictedOwner_adj_iff_crossNeighbor_inter_nonempty]
    refine and_congr_right fun hxy => ?_
    rw [← h.left_common_iff_shadow hxy]
    simp only [componentCrossNeighborFinset, Finset.Nonempty,
      Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, R]
  · intro x y
    rw [restrictedOwner_adj_iff_crossNeighbor_inter_nonempty]
    refine and_congr_right fun hxy => ?_
    rw [← h.right_common_iff_shadow hxy]
    simp only [componentCrossNeighborFinset, Finset.Nonempty,
      Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and, R]
    constructor
    · rintro ⟨z, hxz, hyz⟩
      exact ⟨z, hxz.symm, hyz.symm⟩
    · rintro ⟨z, hzx, hzy⟩
      exact ⟨z, hzx.symm, hzy.symm⟩

end

end Erdos85
