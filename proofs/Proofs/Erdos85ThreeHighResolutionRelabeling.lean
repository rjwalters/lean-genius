import Proofs.Erdos85ThreeHighResolutionDomain

namespace Erdos85

theorem threeHighEligibleTriples_relabel
    (B : Fin 24 → Fin 24 → Bool) (R S : Finset (Fin 24)) (e : Equiv.Perm (Fin 24))
    (hS : S ∈ threeHighEligibleTriples B R) :
    S.image e ∈ threeHighEligibleTriples (fun p q => B (e.symm p) (e.symm q)) (R.image e) := by
  obtain ⟨hsub,hcard,hpair⟩ := (mem_threeHighEligibleTriples B R S).mp hS
  apply (mem_threeHighEligibleTriples _ _ _).mpr
  refine ⟨Finset.image_subset_image hsub, ?_, ?_⟩
  · exact (Finset.card_image_of_injective S e.injective).trans hcard
  · intro a ha b hb hab c hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hb
    apply hpair x hx y hy (fun h => hab (congrArg e h)) (e.symm c)
    simpa only [Equiv.symm_apply_apply] using hp

private theorem image_perm_injective (e : Equiv.Perm (Fin 24)) :
    Function.Injective (fun S : Finset (Fin 24) => S.image e) := by
  intro A B h
  have hh := congrArg (fun S : Finset (Fin 24) => S.image e.symm) h
  simpa only [Finset.image_image, Function.comp_def, Equiv.symm_apply_apply,
    Finset.image_id'] using hh

theorem threeHighResolutionDomain_relabel
    (B : Fin 24 → Fin 24 → Bool) (R : Finset (Fin 24))
    (F : Finset (Finset (Fin 24))) (e : Equiv.Perm (Fin 24))
    (hF : F ∈ threeHighResolutionDomain B R) :
    F.image (fun S => S.image e) ∈
      threeHighResolutionDomain (fun p q => B (e.symm p) (e.symm q)) (R.image e) := by
  obtain ⟨hsub,hcard,hdis,hcover⟩ := (mem_threeHighResolutionDomain B R F).mp hF
  apply (mem_threeHighResolutionDomain _ _ _).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro S hS
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
    exact threeHighEligibleTriples_relabel B R T e (hsub hT)
  · exact (Finset.card_image_of_injective F (image_perm_injective e)).trans hcard
  · intro S hS T hT hST
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨C,hC,rfl⟩ := Finset.mem_image.mp hT
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp hx
    obtain ⟨c,hc,hec⟩ := Finset.mem_image.mp hy
    have hac : a = c := e.injective (hea.trans hec.symm)
    subst c
    exact Finset.disjoint_left.mp (hdis A hA C hC (fun h => hST (congrArg _ h))) ha hc
  · rw [← hcover]
    ext x
    simp only [Finset.mem_biUnion, Finset.mem_image, exists_exists_and_eq_and]
    aesop

end Erdos85
#print axioms Erdos85.threeHighEligibleTriples_relabel
#print axioms Erdos85.threeHighResolutionDomain_relabel
