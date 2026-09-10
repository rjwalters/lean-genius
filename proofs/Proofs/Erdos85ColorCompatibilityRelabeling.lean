import Proofs.Erdos85OrderFortyNineThreeHighTripleColorFamilyCompatibility

namespace Erdos85

theorem encodedCrossIndependent_relabel
    (B : Fin 24 → Fin 24 → Bool) (S T : Finset (Fin 24)) (e : Equiv.Perm (Fin 24)) :
    encodedCrossIndependent (fun i j => B (e.symm i) (e.symm j)) (S.image e) (T.image e) =
      encodedCrossIndependent B S T := by
  unfold encodedCrossIndependent
  apply Bool.decide_congr
  constructor
  · intro h i hi j hj
    simpa only [Equiv.symm_apply_apply] using
      h (e i) (Finset.mem_image.mpr ⟨i,hi,rfl⟩) (e j) (Finset.mem_image.mpr ⟨j,hj,rfl⟩)
  · intro h i hi j hj
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hj
    simpa only [Equiv.symm_apply_apply] using h a ha b hb

theorem encodedFamilyCompatibility_relabel
    (B : Fin 24 → Fin 24 → Bool) (F K : Finset (Finset (Fin 24)))
    (e : Equiv.Perm (Fin 24)) :
    encodedFamilyCompatibility (fun i j => B (e.symm i) (e.symm j))
      (F.image fun S => S.image e) (K.image fun T => T.image e) =
        encodedFamilyCompatibility B F K := by
  unfold encodedFamilyCompatibility
  apply Bool.decide_congr
  constructor
  · intro h S hS
    obtain ⟨T,hT,hgate⟩ := h (S.image e) (Finset.mem_image.mpr ⟨S,hS,rfl⟩)
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hT
    exact ⟨A,hA, by simpa only [encodedCrossIndependent_relabel] using hgate⟩
  · intro h S hS
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨T,hT,hgate⟩ := h A hA
    refine ⟨T.image e, Finset.mem_image.mpr ⟨T,hT,rfl⟩, ?_⟩
    simpa only [encodedCrossIndependent_relabel] using hgate

end Erdos85
#print axioms Erdos85.encodedCrossIndependent_relabel
#print axioms Erdos85.encodedFamilyCompatibility_relabel
