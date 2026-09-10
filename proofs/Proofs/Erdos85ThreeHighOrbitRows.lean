import Proofs.Erdos85ThreeHighCrossRelabeling
import Proofs.Erdos85ThreeBlockOrbitCertificate
import Proofs.Erdos85OrderFortyNineThreeHighTripleCanonicalColorResiduals

namespace Erdos85

theorem threeHighEmptyURelabel_u (e : Equiv.Perm (Fin 15)) (i : Fin 15) :
    threeHighEmptyURelabel e (threeHighEmptyUIndex i) = threeHighEmptyUIndex (e i) := by
  have hinj : Function.Injective threeHighEmptySplit :=
    (Equiv.sumCongr (@finSumFinEquiv 15 8).symm (Equiv.refl (Fin 1))).injective.comp
      (@finSumFinEquiv 23 1).symm.injective
  apply hinj
  simp only [threeHighEmptySplit_relabel,threeHighEmptySplit_u,Sum.map_inl]

theorem threeHighEmptyURelabel_symm (e : Equiv.Perm (Fin 15)) :
    threeHighEmptyURelabel e.symm = (threeHighEmptyURelabel e).symm := by
  rfl

/-- The production orbit label exchanges only rows one/two and permutes columns. -/
theorem threeHighOrbitLabel_rows (p : Fin 120) (sw : Bool) (k : Fin 3) :
    (threeHighCanonicalRow k).image (threeHighEmptyURelabel (threeBlockOrbitLabel p sw)) =
      threeHighCanonicalRow ((if sw then Equiv.swap 1 2 else Equiv.refl (Fin 3)) k) := by
  classical
  ext x
  simp only [threeHighCanonicalRow,Finset.image_image,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,rfl⟩
    refine ⟨finFivePermutationCode p i,?_⟩
    simp [threeHighEmptyURelabel_u,threeBlockOrbitLabel,Equiv.trans_apply]
  · rintro ⟨i,rfl⟩
    refine ⟨(finFivePermutationCode p).symm i,?_⟩
    simp [threeHighEmptyURelabel_u,threeBlockOrbitLabel,Equiv.trans_apply]

end Erdos85
#print axioms Erdos85.threeHighEmptyURelabel_u
#print axioms Erdos85.threeHighEmptyURelabel_symm
#print axioms Erdos85.threeHighOrbitLabel_rows
