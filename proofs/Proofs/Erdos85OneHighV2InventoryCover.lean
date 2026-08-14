import Proofs.Erdos85OneHighV2Cp4Action
import Proofs.Erdos85OneHighV2EnumCompleteness
import Proofs.Erdos85OneHighV2Inventory

/-! # Connecting the executable CP4 classifier to the stored inventory -/

namespace Erdos85

/-- Restriction to the 24 relevant coordinates commutes with the CP4 action. -/
theorem OneHighFamilyV2Admissible.toFinite_permute {profile : Nat}
    {table : OneHighMissTable}
    (h : OneHighFamilyV2Admissible profile table)
    (σ : OneHighProfilePerm profile) :
    (h.permute σ).toFinite = oneHighFinitePermute σ.1 h.toFinite := by
  funext pair
  apply Fin.ext
  rw [OneHighFamilyV2Admissible.toFinite_apply]
  unfold oneHighFinitePermute
  rw [OneHighFamilyV2Admissible.toFinite_apply]
  rw [OneHighProfilePerm.permuteTable_apply]
  change table (σ.1.symm pair.1.1).val (σ.1.symm pair.1.2).val =
    table
      (oneHighRelevantPairMap σ.1.symm pair).1.1.val
      (oneHighRelevantPairMap σ.1.symm pair).1.2.val
  rcases oneHighRelevantPairMap_spec (π := σ.1.symm) σ.inv.2.1 pair with
    hmap | hmap
  · rw [hmap]
  · rw [hmap]
    exact h.symm (σ.1.symm pair.1.1) (σ.1.symm pair.1.2)
      (fun heq => Fin.ne_of_lt pair.2.1 (σ.1.symm.injective heq).symm)
      (by
        intro heq
        apply pair.2.2
        have himage := congrArg σ.1 heq
        simpa [σ.2.1] using himage)

end Erdos85
