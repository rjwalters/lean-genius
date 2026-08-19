import Proofs.Erdos85BipartiteTwoRegularMatchingBridge
import Proofs.Erdos85TwoIncidenceShadowRegular

/-! # Isomorphic shore shadows of a two-regular bipartite relation

After choosing one perfect matching, every edge of a two-regular bipartite
relation lies in that matching or in its residual perfect matching.  The
chosen matching consequently transports common-neighbor adjacency from one
shore to the other.
-/

namespace Erdos85

open SimpleGraph

theorem BipartiteTwoRegularAfterMatching.rel_iff
    {S T : Type*} {R : S → T → Prop} {f : S ≃ T}
    (h : BipartiteTwoRegularAfterMatching R f) (s : S) (t : T) :
    R s t ↔ t = f s ∨ t = h.residualEquiv s := by
  constructor
  · intro hst
    by_cases htf : t = f s
    · exact Or.inl htf
    · exact Or.inr <| (h.residual_unique_left s).unique
        ⟨hst, htf⟩ (h.residualEquiv_mem s)
  · rintro (rfl | rfl)
    · exact h.matching_mem s
    · exact (h.residualEquiv_mem s).1

/-- A displayed perfect matching transports the common-neighbor shadow on
one shore of a two-regular bipartite relation to the shadow on the other. -/
noncomputable def BipartiteTwoRegularAfterMatching.shadowIso
    {S T : Type*} {R : S → T → Prop} {f : S ≃ T}
    (h : BipartiteTwoRegularAfterMatching R f) :
    twoIncidenceShadow R ≃g
      twoIncidenceShadow (fun t s => R s t) where
  toEquiv := f
  map_rel_iff' := by
    intro x y
    constructor
    · rintro ⟨hxy, z, hzx, hzy⟩
      have hzx' := (h.rel_iff z (f x)).mp hzx
      have hzy' := (h.rel_iff z (f y)).mp hzy
      have hxy' : x ≠ y := fun hEq => hxy (congrArg f hEq)
      refine ⟨hxy', ?_⟩
      rcases hzx' with hxz | hxz <;> rcases hzy' with hyz | hyz
      · exact (hxy (hxz.trans hyz.symm)).elim
      · refine ⟨f y, ?_, h.matching_mem y⟩
        have hzxEq : z = x := (f.injective hxz).symm
        subst z
        exact hyz ▸ (h.residualEquiv_mem x).1
      · refine ⟨f x, h.matching_mem x, ?_⟩
        have hzyEq : z = y := (f.injective hyz).symm
        subst z
        exact hxz ▸ (h.residualEquiv_mem y).1
      · exact (hxy (hxz.trans hyz.symm)).elim
    · rintro ⟨hxy, t, hxt, hyt⟩
      have hxt' := (h.rel_iff x t).mp hxt
      have hyt' := (h.rel_iff y t).mp hyt
      have hfxy : f x ≠ f y := fun hEq => hxy (f.injective hEq)
      refine ⟨hfxy, ?_⟩
      rcases hxt' with htx | htx <;> rcases hyt' with hty | hty
      · exact (hxy (f.injective (htx.symm.trans hty))).elim
      · refine ⟨y, ?_, h.matching_mem y⟩
        have hEq : f x = h.residualEquiv y := htx.symm.trans hty
        exact hEq.symm ▸ (h.residualEquiv_mem y).1
      · refine ⟨x, h.matching_mem x, ?_⟩
        have hEq : h.residualEquiv x = f y := htx.symm.trans hty
        exact hEq ▸ (h.residualEquiv_mem x).1
      · exact (hxy (h.residualEquiv.injective (htx.symm.trans hty))).elim

end Erdos85

#print axioms Erdos85.BipartiteTwoRegularAfterMatching.shadowIso
