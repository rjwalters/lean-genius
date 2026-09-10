import Proofs.Erdos85ThreeBlockCompactCodes
import Proofs.Erdos85ThreeBlockOrbitCertificate

namespace Erdos85

def threeBlockCompactAdj (p : ThreeBlockFirstRowParameters) (x y : Fin 15) : Bool :=
  threeBlockFullParameterAdj (threeBlockFirstRowEmbed p)
    ((@finProdFinEquiv 3 5).symm x) ((@finProdFinEquiv 3 5).symm y)

def threeBlockDeficientCompactAdj (p : ThreeBlockDeficientFirstRowParameters)
    (x y : Fin 15) : Bool :=
  threeBlockDeficientParameterAdj (threeBlockDeficientFirstRowEmbed p)
    ((@finProdFinEquiv 3 5).symm x) ((@finProdFinEquiv 3 5).symm y)

/-- Exhaustive code certificates give coverage for arbitrary compact parameters.
The finite certificate validity premise must still be checked by an application. -/
theorem threeBlockCompactOrbitCover {n : Nat}
    (reps : Fin n → Fin 15 → Fin 15 → Bool)
    (cert : Fin 15 → Fin 15 → Fin 120 → ThreeBlockOrbitCertificate n)
    (checked : ∀ a b i, (cert a b i).Valid
      (threeBlockCompactAdj (threeBlockCompactCode a b i)) reps)
    (p : ThreeBlockFirstRowParameters)
    (hfree : encodedC4Free (threeBlockCompactAdj p) = true) :
    ∃ (r : Fin n) (q : Fin 120) (sw : Bool), ∀ x y,
      threeBlockCompactAdj p x y =
        reps r (threeBlockOrbitLabel q sw x) (threeBlockOrbitLabel q sw y) := by
  obtain ⟨a,b,i,rfl⟩ := threeBlockCompactCode_covers p
  exact (cert a b i).covered _ reps (checked a b i) hfree

/-- Deficient coverage also enumerates the missing source label. -/
theorem threeBlockDeficientCompactOrbitCover {n : Nat}
    (reps : Fin n → Fin 15 → Fin 15 → Bool)
    (cert : Fin 15 → Fin 15 → Fin 120 → Fin 5 → ThreeBlockOrbitCertificate n)
    (checked : ∀ a b i d, (cert a b i d).Valid
      (threeBlockDeficientCompactAdj (threeBlockDeficientCompactCode a b i d)) reps)
    (p : ThreeBlockDeficientFirstRowParameters)
    (hfree : encodedC4Free (threeBlockDeficientCompactAdj p) = true) :
    ∃ (r : Fin n) (q : Fin 120) (sw : Bool), ∀ x y,
      threeBlockDeficientCompactAdj p x y =
        reps r (threeBlockOrbitLabel q sw x) (threeBlockOrbitLabel q sw y) := by
  obtain ⟨a,b,i,d,rfl⟩ := threeBlockDeficientCompactCode_covers p
  exact (cert a b i d).covered _ reps (checked a b i d) hfree

end Erdos85
#print axioms Erdos85.threeBlockCompactOrbitCover
#print axioms Erdos85.threeBlockDeficientCompactOrbitCover
