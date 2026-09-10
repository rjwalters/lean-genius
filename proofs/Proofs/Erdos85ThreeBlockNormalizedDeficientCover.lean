import Proofs.Erdos85ThreeBlockCompactSourceNormalization
import Proofs.Erdos85ThreeBlockDisjointMaskCodes

namespace Erdos85

/-- Only 100 mask pairs and the two normalized missing sources need certificates.
The normalization and orbit actions compose into a production orbit action. -/
theorem threeBlockNormalizedDeficientOrbitCover {n : Nat}
    (reps : Fin n → Fin 15 → Fin 15 → Bool)
    (cert : Fin 15 → Fin 15 → Fin 120 → Fin 5 → ThreeBlockOrbitCertificate n)
    (checked : ∀ a b i d, (a,b) ∈ threeBlockDisjointMaskPairs → (d = 0 ∨ d = 4) →
      (cert a b i d).Valid
        (threeBlockDeficientCompactAdj (threeBlockDeficientCompactCode a b i d)) reps)
    (p : ThreeBlockDeficientFirstRowParameters)
    (hf : encodedC4Free (threeBlockDeficientCompactAdj p) = true) :
    ∃ (r : Fin n) (s : Fin 120) (sw : Bool), ∀ x y,
      threeBlockDeficientCompactAdj p x y =
        reps r (threeBlockOrbitLabel s sw x) (threeBlockOrbitLabel s sw y) := by
  obtain ⟨q,hd,hqfree,hpq⟩ := threeBlockDeficientCompact_source_normalize p hf
  obtain ⟨a,b,i,d,hq⟩ := threeBlockDeficientCompactCode_covers q
  subst q
  have hm := threeBlockDeficientCompactCode_disjoint_masks a b i d
    ((encodedC4Free_relabel _ (@finProdFinEquiv 3 5).symm).symm.trans hqfree)
  obtain ⟨r,t,sw,hr⟩ := (cert a b i d).covered _ reps (checked a b i d hm hd) hqfree
  obtain ⟨s,hs⟩ := threeBlockOrbitLabel_diagonal_trans (threeBlockSourceNormalizerCode p.2) t sw
  refine ⟨r,s,sw,?_⟩
  intro x y
  simpa only [hs,Equiv.trans_apply] using
    (hpq x y).trans (hr (threeBlockOrbitLabel (threeBlockSourceNormalizerCode p.2) false x)
      (threeBlockOrbitLabel (threeBlockSourceNormalizerCode p.2) false y))

end Erdos85
#print axioms Erdos85.threeBlockNormalizedDeficientOrbitCover
