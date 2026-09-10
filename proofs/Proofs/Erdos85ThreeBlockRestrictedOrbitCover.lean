import Proofs.Erdos85ThreeBlockCompactOrbitCover
import Proofs.Erdos85ThreeBlockDisjointMaskCodes
import Proofs.Erdos85EncodedRelabeling

namespace Erdos85

/-- Certificates for only the 100 disjoint mask pairs cover arbitrary compact parameters.
Validity on that restricted domain remains an explicit application obligation. -/
theorem threeBlockRestrictedOrbitCover {n : Nat}
    (reps : Fin n → Fin 15 → Fin 15 → Bool)
    (cert : Fin 15 → Fin 15 → Fin 120 → ThreeBlockOrbitCertificate n)
    (checked : ∀ a b i, (a,b) ∈ threeBlockDisjointMaskPairs → (cert a b i).Valid
      (threeBlockCompactAdj (threeBlockCompactCode a b i)) reps)
    (p : ThreeBlockFirstRowParameters)
    (hfree : encodedC4Free (threeBlockCompactAdj p) = true) :
    ∃ (r : Fin n) (q : Fin 120) (sw : Bool), ∀ x y,
      threeBlockCompactAdj p x y =
        reps r (threeBlockOrbitLabel q sw x) (threeBlockOrbitLabel q sw y) := by
  obtain ⟨a,b,i,rfl⟩ := threeBlockCompactCode_covers p
  have hm := threeBlockCompactCode_disjoint_masks a b i
    ((encodedC4Free_relabel _ (@finProdFinEquiv 3 5).symm).symm.trans hfree)
  exact (cert a b i).covered _ reps (checked a b i hm) hfree

/-- Deficient coverage needs only the 100 disjoint mask pairs and five missing sources. -/
theorem threeBlockDeficientRestrictedOrbitCover {n : Nat}
    (reps : Fin n → Fin 15 → Fin 15 → Bool)
    (cert : Fin 15 → Fin 15 → Fin 120 → Fin 5 → ThreeBlockOrbitCertificate n)
    (checked : ∀ a b i d, (a,b) ∈ threeBlockDisjointMaskPairs → (cert a b i d).Valid
      (threeBlockDeficientCompactAdj (threeBlockDeficientCompactCode a b i d)) reps)
    (p : ThreeBlockDeficientFirstRowParameters)
    (hfree : encodedC4Free (threeBlockDeficientCompactAdj p) = true) :
    ∃ (r : Fin n) (q : Fin 120) (sw : Bool), ∀ x y,
      threeBlockDeficientCompactAdj p x y =
        reps r (threeBlockOrbitLabel q sw x) (threeBlockOrbitLabel q sw y) := by
  obtain ⟨a,b,i,d,rfl⟩ := threeBlockDeficientCompactCode_covers p
  have hm := threeBlockDeficientCompactCode_disjoint_masks a b i d
    ((encodedC4Free_relabel _ (@finProdFinEquiv 3 5).symm).symm.trans hfree)
  exact (cert a b i d).covered _ reps (checked a b i d hm) hfree

end Erdos85
#print axioms Erdos85.threeBlockRestrictedOrbitCover
#print axioms Erdos85.threeBlockDeficientRestrictedOrbitCover
