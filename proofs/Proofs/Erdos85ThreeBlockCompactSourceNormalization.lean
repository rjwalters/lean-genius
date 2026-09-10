import Proofs.Erdos85ThreeBlockDeficientSourceNormalization
import Proofs.Erdos85ThreeBlockCompactOrbitCover

namespace Erdos85

/-- A diagonal normalization followed by a production orbit action is another
production orbit action, retaining the optional row swap. -/
theorem threeBlockOrbitLabel_diagonal_trans (s t : Fin 120) (sw : Bool) :
    ∃ q : Fin 120, threeBlockOrbitLabel q sw =
      (threeBlockOrbitLabel s false).trans (threeBlockOrbitLabel t sw) := by
  obtain ⟨q,hq⟩ := finFivePermutationCode_surjective
    ((finFivePermutationCode s).trans (finFivePermutationCode t))
  refine ⟨q,?_⟩
  ext x
  simp [threeBlockOrbitLabel,Equiv.trans_apply,hq,Prod.map]

attribute [local irreducible] threeBlockDeficientCandidates encodedC4Free

theorem threeBlockDeficientCompact_source_normalize
    (p : ThreeBlockDeficientFirstRowParameters)
    (hf : encodedC4Free (threeBlockDeficientCompactAdj p) = true) :
    ∃ q : ThreeBlockDeficientFirstRowParameters,
      (q.2 = 0 ∨ q.2 = 4) ∧
      encodedC4Free (threeBlockDeficientCompactAdj q) = true ∧
      ∀ x y, threeBlockDeficientCompactAdj p x y =
        threeBlockDeficientCompactAdj q
          (threeBlockOrbitLabel (threeBlockSourceNormalizerCode p.2) false x)
          (threeBlockOrbitLabel (threeBlockSourceNormalizerCode p.2) false y) := by
  have hp : threeBlockDeficientFirstRowEmbed p ∈ threeBlockDeficientCandidates := by
    apply (threeBlockDeficientCandidates_mem_iff _).mpr
    exact (encodedC4Free_relabel _ (@finProdFinEquiv 3 5).symm).symm.trans hf
  obtain ⟨p',hp',hz,hd,ha⟩ := threeBlockDeficientCandidates_source_normalize
    (threeBlockDeficientFirstRowEmbed p) hp rfl
  obtain ⟨q,hq⟩ := threeBlockDeficientFirstRowEmbed_cover p' hz
  subst p'
  refine ⟨q,hd,?_,?_⟩
  · exact (encodedC4Free_relabel _ (@finProdFinEquiv 3 5).symm).trans
      ((threeBlockDeficientCandidates_mem_iff _).mp hp')
  · intro x y
    simpa [threeBlockDeficientCompactAdj,threeBlockOrbitLabel,Equiv.trans_apply,
      Prod.map,threeBlockDeficientFirstRowEmbed] using
      ha ((@finProdFinEquiv 3 5).symm x) ((@finProdFinEquiv 3 5).symm y)

end Erdos85
#print axioms Erdos85.threeBlockOrbitLabel_diagonal_trans
#print axioms Erdos85.threeBlockDeficientCompact_source_normalize
