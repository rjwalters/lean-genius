import Proofs.Erdos85ThreeBlockMaskRelabeling
import Proofs.Erdos85ThreeBlockDiagonalRelabeling
import Proofs.Erdos85EncodedRelabeling

namespace Erdos85
noncomputable section

/-- Normalize one row using a single diagonal permutation on all three rows. -/
theorem threeBlockMasks_first_row (masks : Fin 3 → ThreeBlockMask) :
    ∃ (σ : Equiv.Perm (Fin 5)) (masks' : Fin 3 → ThreeBlockMask),
      masks' 0 = threeBlockCanonicalMask ∧ ∀ k i j,
        oneHighBranchBitAdj (masks k).val i j =
          oneHighBranchBitAdj (masks' k).val (σ i) (σ j) := by
  classical
  obtain ⟨σ,hσ⟩ := threeBlockMask_to_canonical (masks 0)
  choose mm hmm using fun k => threeBlockMask_relabel (masks k) σ
  let masks' := fun k => if k = 0 then threeBlockCanonicalMask else mm k
  refine ⟨σ,masks',by simp [masks'],?_⟩
  intro k i j
  by_cases hk : k = 0
  · subst k
    simpa only [masks',if_pos rfl] using hσ i j
  · simpa only [masks',if_neg hk,Equiv.symm_apply_apply] using (hmm k (σ i) (σ j)).symm

attribute [local irreducible] threeBlockFullCandidates threeBlockDeficientCandidates encodedC4Free

theorem threeBlockFullCandidates_first_row
    (p : ThreeBlockFullParameters) (hp : p ∈ threeBlockFullCandidates) :
    ∃ (p' : ThreeBlockFullParameters) (σ : Equiv.Perm (Fin 5)),
      p' ∈ threeBlockFullCandidates ∧ p'.1 0 = threeBlockCanonicalMask ∧
      ∀ a b, threeBlockFullParameterAdj p a b =
        threeBlockFullParameterAdj p' (a.1,σ a.2) (b.1,σ b.2) := by
  obtain ⟨σ,masks',hzero,hmask⟩ := threeBlockMasks_first_row p.1
  let p' : ThreeBlockFullParameters := (masks',threeBlockConjugate p.2 σ)
  have ha (a b) : threeBlockFullParameterAdj p a b =
      threeBlockFullParameterAdj p' (a.1,σ a.2) (b.1,σ b.2) :=
    threeBlockMatchingAdj_diagonal_relabel _ _ p.2 σ hmask a b
  let e : Equiv.Perm (Fin 3 × Fin 5) := Equiv.prodCongr (Equiv.refl _) σ
  have hfun : (fun a b => threeBlockFullParameterAdj p (e.symm a) (e.symm b)) =
      threeBlockFullParameterAdj p' := by
    funext a b
    simpa [e] using ha (e.symm a) (e.symm b)
  have hc := encodedC4Free_comap_injective (threeBlockFullParameterAdj p) e.symm e.symm.injective
    ((threeBlockFullCandidates_mem_iff p).mp hp)
  refine ⟨p',σ,?_,hzero,ha⟩
  apply (threeBlockFullCandidates_mem_iff p').mpr
  simpa only [hfun] using hc

theorem threeBlockDeficientCandidates_first_row
    (p : ThreeBlockDeficientParameters) (hp : p ∈ threeBlockDeficientCandidates) :
    ∃ (p' : ThreeBlockDeficientParameters) (σ : Equiv.Perm (Fin 5)),
      p' ∈ threeBlockDeficientCandidates ∧ p'.1.1 0 = threeBlockCanonicalMask ∧
      ∀ a b, threeBlockDeficientParameterAdj p a b =
        threeBlockDeficientParameterAdj p' (a.1,σ a.2) (b.1,σ b.2) := by
  obtain ⟨σ,masks',hzero,hmask⟩ := threeBlockMasks_first_row p.1.1
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
  refine ⟨p',σ,?_,hzero,ha⟩
  apply (threeBlockDeficientCandidates_mem_iff p').mpr
  simpa only [hfun] using hc

end
end Erdos85
#print axioms Erdos85.threeBlockMasks_first_row
#print axioms Erdos85.threeBlockFullCandidates_first_row
#print axioms Erdos85.threeBlockDeficientCandidates_first_row
