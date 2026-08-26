import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalSemanticEmptyAdmissible
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyPermutationAction
import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalSemanticEmptyOrbitRelabel

/-! # Semantic consumer of the checked canonical empty-mask orbit cover -/

namespace Erdos85

open SimpleGraph

/-- Membership in the flattened representative table recovers the external
edge-count/type coordinates and their exact bounds. -/
theorem sevenHighT0CanonicalEmptyRepresentative_mem_data
    (representative : SevenHighT0CanonicalEmptyRepresentative)
    (hrepresentative :
      representative ∈ sevenHighT0CanonicalEmptyRepresentatives) :
    6 ≤ representative.edgeCount ∧ representative.edgeCount ≤ 9 ∧
      representative.typeIndex <
        (sevenHighT0CanonicalEmptyRepresentativeMasks
          representative.edgeCount).length ∧
      representative.mask = sevenHighT0CanonicalEmptyRepresentativeMask
        representative.edgeCount representative.typeIndex := by
  rw [sevenHighT0CanonicalEmptyRepresentatives,
    List.mem_flatMap] at hrepresentative
  obtain ⟨offset, hoffset, hrepresentative⟩ := hrepresentative
  rw [List.mem_map] at hrepresentative
  obtain ⟨typeIndex, htypeIndex, rfl⟩ := hrepresentative
  have hoffsetLt : offset < 4 := List.mem_range.mp hoffset
  have htypeIndexLt := List.mem_range.mp htypeIndex
  change 6 ≤ offset + 6 ∧ offset + 6 ≤ 9 ∧
    typeIndex <
      (sevenHighT0CanonicalEmptyRepresentativeMasks (offset + 6)).length ∧
    sevenHighT0CanonicalEmptyRepresentativeMask (offset + 6) typeIndex =
      sevenHighT0CanonicalEmptyRepresentativeMask (offset + 6) typeIndex
  exact ⟨by omega, by omega, htypeIndexLt, rfl⟩

/-- Every canonical completion can be relabeled so that its semantic empty
mask is one of the 43 pinned representatives, with the precise cube-table
coordinates exposed. -/
theorem SevenHighT0CanonicalCompletionSemantics.exists_relabel_emptyRepresentative
    {H : SimpleGraph SevenHighT0CanonicalIndex} [DecidableRel H.Adj]
    (semantics : SevenHighT0CanonicalCompletionSemantics H) :
    ∃ edgeCount, 6 ≤ edgeCount ∧ edgeCount ≤ 9 ∧
      ∃ typeIndex,
        typeIndex <
          (sevenHighT0CanonicalEmptyRepresentativeMasks edgeCount).length ∧
        ∃ σ : Equiv.Perm (Fin 7),
          SevenHighT0CanonicalCompletionSemantics
            (sevenHighT0CanonicalRelabel σ H) ∧
          sevenHighT0CanonicalEmptySemanticMask
              (sevenHighT0CanonicalRelabel σ H) =
            sevenHighT0CanonicalEmptyRepresentativeMask
              edgeCount typeIndex := by
  obtain ⟨representative, hrepresentative,
      permutation, hpermutation, hmask⟩ :=
    sevenHighT0CanonicalEmptyAdmissible_exists_representative_permutation
      semantics.semanticEmptyMask_admissible
  let rowEquiv := sevenHighT0CanonicalPermutationRowEquiv
    permutation hpermutation
  have hrelabelMask :
      sevenHighT0CanonicalEmptySemanticMask
          (sevenHighT0CanonicalRelabel rowEquiv.symm H) =
        representative.mask := by
    apply sevenHighT0CanonicalEmptySemanticMask_relabel_eq_of_adj
      H rowEquiv.symm representative.mask
      (sevenHighT0CanonicalEmptyRepresentative_mask_lt
        representative hrepresentative)
    intro left right
    change sevenHighT0CanonicalEmptyAdj
        representative.mask left.val right.val =
      sevenHighT0CanonicalEmptyAdj
        (sevenHighT0CanonicalEmptySemanticMask H)
        (rowEquiv left).val (rowEquiv right).val
    rw [hmask]
    exact (sevenHighT0CanonicalEmptyPermutedMask_adj
      representative hrepresentative permutation hpermutation
      left right).symm
  obtain ⟨hedgeLow, hedgeHigh, htypeIndex, hrepresentativeMask⟩ :=
    sevenHighT0CanonicalEmptyRepresentative_mem_data
      representative hrepresentative
  refine ⟨representative.edgeCount, hedgeLow, hedgeHigh,
    representative.typeIndex, htypeIndex, rowEquiv.symm,
    semantics.relabel rowEquiv.symm, ?_⟩
  exact hrelabelMask.trans hrepresentativeMask

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEmptyRepresentative_mem_data
#print axioms Erdos85.SevenHighT0CanonicalCompletionSemantics.exists_relabel_emptyRepresentative
