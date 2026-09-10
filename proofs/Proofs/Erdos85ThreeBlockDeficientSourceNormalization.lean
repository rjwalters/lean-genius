import Proofs.Erdos85ThreeBlockStabilizerRelabeling
import Proofs.Erdos85FinFivePermutationCodes

namespace Erdos85

def threeBlockSourceNormalizerCode (d : Fin 5) : Fin 120 := ![0,24,60,86,0] d

set_option maxRecDepth 100000 in
theorem threeBlockSourceNormalizer_stabilizer (d : Fin 5) :
    finFivePermutationCode (threeBlockSourceNormalizerCode d) ∈ threeBlockCanonicalStabilizer := by
  apply (mem_threeBlockCanonicalStabilizer _).mpr
  intro i j
  decide +revert

set_option maxRecDepth 100000 in
theorem threeBlockSourceNormalizer_source (d : Fin 5) :
    finFivePermutationCode (threeBlockSourceNormalizerCode d) d = 0 ∨
      finFivePermutationCode (threeBlockSourceNormalizerCode d) d = 4 := by
  decide +revert

attribute [local irreducible] threeBlockDeficientCandidates encodedC4Free

/-- Normalize the missing source to zero or the isolated first-row label four.
The same diagonal relabeling preserves the canonical first-row matching. -/
theorem threeBlockDeficientCandidates_source_normalize
    (p : ThreeBlockDeficientParameters) (hp : p ∈ threeBlockDeficientCandidates)
    (hzero : p.1.1 0 = threeBlockCanonicalMask) :
    ∃ (p' : ThreeBlockDeficientParameters),
      p' ∈ threeBlockDeficientCandidates ∧ p'.1.1 0 = threeBlockCanonicalMask ∧
      (p'.2 = 0 ∨ p'.2 = 4) ∧
      ∀ a b, threeBlockDeficientParameterAdj p a b =
        threeBlockDeficientParameterAdj p'
          (a.1,finFivePermutationCode (threeBlockSourceNormalizerCode p.2) a.2)
          (b.1,finFivePermutationCode (threeBlockSourceNormalizerCode p.2) b.2) := by
  let σ := finFivePermutationCode (threeBlockSourceNormalizerCode p.2)
  obtain ⟨masks',hzero',hmask⟩ := threeBlockMasks_stabilizer p.1.1 hzero σ
    (threeBlockSourceNormalizer_stabilizer p.2)
  let p' : ThreeBlockDeficientParameters := ((masks',threeBlockConjugate p.1.2 σ),σ p.2)
  have ha (a b) : threeBlockDeficientParameterAdj p a b =
      threeBlockDeficientParameterAdj p' (a.1,σ a.2) (b.1,σ b.2) :=
    threeBlockDeficientMatchingAdj_diagonal_relabel _ _ p.1.2 σ p.2 hmask a b
  let e : Equiv.Perm (Fin 3 × Fin 5) := Equiv.prodCongr (Equiv.refl _) σ
  have hfun : (fun a b => threeBlockDeficientParameterAdj p (e.symm a) (e.symm b)) =
      threeBlockDeficientParameterAdj p' := by
    funext a b
    simpa [e] using ha (e.symm a) (e.symm b)
  have hc := encodedC4Free_comap_injective (threeBlockDeficientParameterAdj p) e.symm e.symm.injective
    ((threeBlockDeficientCandidates_mem_iff p).mp hp)
  refine ⟨p',?_,hzero',threeBlockSourceNormalizer_source p.2,ha⟩
  apply (threeBlockDeficientCandidates_mem_iff p').mpr
  simpa only [hfun] using hc

end Erdos85
#print axioms Erdos85.threeBlockSourceNormalizer_stabilizer
#print axioms Erdos85.threeBlockSourceNormalizer_source
#print axioms Erdos85.threeBlockDeficientCandidates_source_normalize
