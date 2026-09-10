import Proofs.Erdos85OrderFortyNineThreeHighTripleTerminalCertificate
import Proofs.Erdos85ThreeHighResolutionRelabeling
import Proofs.Erdos85BlockCapRelabeling
import Proofs.Erdos85ColorCompatibilityRelabeling

namespace Erdos85

theorem threeHighCanonicalResidual_relabel
    (e : Equiv.Perm (Fin 24)) (σ : Equiv.Perm (Fin 3))
    (hroot : e 23 = 23)
    (hrows : ∀ k, (threeHighCanonicalRow k).image e = threeHighCanonicalRow (σ k))
    (k : Fin 3) :
    (threeHighCanonicalResidual k).image e = threeHighCanonicalResidual (σ k) := by
  simp only [threeHighCanonicalResidual,Finset.image_sdiff _ _ e.injective,
    Finset.image_union,Finset.image_singleton,hroot,hrows]
  rw [Finset.image_univ_equiv]

/-- Transport all three resolution families together, including both compatibility
conditions, when a vertex permutation fixes the root and permutes canonical blocks. -/
theorem ThreeHighJointWitness.relabel
    (B : Fin 24 → Fin 24 → Bool) (hB : ThreeHighJointWitness B)
    (e : Equiv.Perm (Fin 24)) (σ : Equiv.Perm (Fin 3))
    (hroot : e 23 = 23)
    (hrows : ∀ k, (threeHighCanonicalRow k).image e = threeHighCanonicalRow (σ k)) :
    ThreeHighJointWitness (fun x y => B (e.symm x) (e.symm y)) := by
  classical
  obtain ⟨F,hF,hblock,hcompat,hcap⟩ := hB
  refine ⟨fun k => (F (σ.symm k)).image (fun S => S.image e),?_,?_,?_,?_⟩
  · intro k
    have h := threeHighResolutionDomain_relabel B (threeHighCanonicalResidual (σ.symm k))
      (F (σ.symm k)) e (hF (σ.symm k))
    simpa only [threeHighCanonicalResidual_relabel e σ hroot hrows,Equiv.apply_symm_apply] using h
  · intro k S hS
    obtain ⟨T,hT,rfl⟩ := Finset.mem_image.mp hS
    have h := encodedTripleBlockCap_relabel threeHighCanonicalRow T e
    have ht := hblock (σ.symm k) T hT
    unfold encodedTripleBlockCap at h ht ⊢
    apply decide_eq_true_iff.mpr
    intro j
    have hsrc : ∀ j, (T.image e ∩ (threeHighCanonicalRow j).image e).card ≤ 1 := by
      apply of_decide_eq_true
      exact h.trans ht
    simpa only [hrows,Equiv.apply_symm_apply] using hsrc (σ.symm j)
  · intro i j
    simpa only [encodedFamilyCompatibility_relabel] using hcompat (σ.symm i) (σ.symm j)
  · intro i j hij
    unfold encodedFamilyIntersectionCap
    apply decide_eq_true_iff.mpr
    apply (family_inter_cap_relabel (F (σ.symm i)) (F (σ.symm j)) e).mpr
    exact of_decide_eq_true (hcap (σ.symm i) (σ.symm j) (fun h => hij (σ.symm.injective h)))

end Erdos85
#print axioms Erdos85.threeHighCanonicalResidual_relabel
#print axioms Erdos85.ThreeHighJointWitness.relabel
