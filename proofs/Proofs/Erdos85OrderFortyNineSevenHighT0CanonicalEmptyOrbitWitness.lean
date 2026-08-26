import Proofs.Erdos85OrderFortyNineSevenHighT0CanonicalEmptyOrbitCover
import Mathlib.Data.List.GetD

namespace Erdos85

noncomputable section

/-- Turn one executable permutation row into the corresponding permutation
of `Fin 7`. -/
noncomputable def sevenHighT0CanonicalPermutationRowEquiv
    (permutation : List Nat)
    (hpermutation : permutation ∈ sevenHighT0CanonicalPermutationRows) :
    Equiv.Perm (Fin 7) := by
  have hperm : permutation.Perm (List.range 7) := by
    exact List.mem_permutations.mp hpermutation
  have hlength : permutation.length = 7 := hperm.length_eq
  have hnodup : permutation.Nodup :=
    hperm.nodup_iff.mpr List.nodup_range
  let index : Fin 7 → Fin permutation.length := fun i =>
    ⟨i.val, by omega⟩
  let f : Fin 7 → Fin 7 := fun i =>
    ⟨permutation.get (index i), by
      have hmem : permutation.get (index i) ∈ permutation :=
        permutation.get_mem (index i)
      exact List.mem_range.mp (hperm.mem_iff.mp hmem)⟩
  have hinjective : Function.Injective f := by
    intro i j hij
    have hget : permutation.get (index i) =
        permutation.get (index j) := congrArg Fin.val hij
    have hindex : index i = index j := hnodup.injective_get hget
    apply Fin.ext
    exact congrArg (fun k : Fin permutation.length => k.val) hindex
  exact Equiv.ofBijective f
    ((Fintype.bijective_iff_injective_and_card f).2
      ⟨hinjective, rfl⟩)

theorem sevenHighT0CanonicalPermutationRowEquiv_apply
    (permutation : List Nat)
    (hpermutation : permutation ∈ sevenHighT0CanonicalPermutationRows)
    (i : Fin 7) :
    (sevenHighT0CanonicalPermutationRowEquiv
      permutation hpermutation i).val = permutation.getD i.val 0 := by
  have hperm : permutation.Perm (List.range 7) :=
    List.mem_permutations.mp hpermutation
  have hlength : permutation.length = 7 := hperm.length_eq
  change permutation.get ⟨i.val, by omega⟩ = permutation.getD i.val 0
  symm
  exact List.getD_eq_get (l := permutation) (d := 0)
    ⟨i.val, by omega⟩

/-- Witness-producing form of the checked orbit cover. -/
theorem sevenHighT0CanonicalEmptyAdmissible_exists_representative_permutation
    {mask : Nat} (hmask : sevenHighT0CanonicalEmptyAdmissible mask = true) :
    ∃ representative ∈ sevenHighT0CanonicalEmptyRepresentatives,
      ∃ permutation ∈ sevenHighT0CanonicalPermutationRows,
        mask = sevenHighT0CanonicalEmptyPermutedMask
          permutation representative.mask := by
  have hconditions := hmask
  simp only [sevenHighT0CanonicalEmptyAdmissible, Bool.and_eq_true,
    decide_eq_true_eq] at hconditions
  have hlt : mask < 2 ^ 21 := hconditions.1.1.1
  have hmemAdmissible :
      mask ∈ sevenHighT0CanonicalEmptyAdmissibleMasks := by
    rw [sevenHighT0CanonicalEmptyAdmissibleMasks, List.mem_filter]
    exact ⟨List.mem_range.mpr hlt, hmask⟩
  have hmemOrbitFinset :
      mask ∈ sevenHighT0CanonicalEmptyRepresentativeOrbitMasks.toFinset := by
    rw [← sevenHighT0CanonicalEmptyRepresentative_orbit_cover]
    exact List.mem_toFinset.mpr hmemAdmissible
  have hmemOrbit :
      mask ∈ sevenHighT0CanonicalEmptyRepresentativeOrbitMasks :=
    List.mem_toFinset.mp hmemOrbitFinset
  rw [sevenHighT0CanonicalEmptyRepresentativeOrbitMasks,
    List.mem_flatMap] at hmemOrbit
  rcases hmemOrbit with ⟨representative, hrepresentative, hmemPerm⟩
  rw [List.mem_map] at hmemPerm
  rcases hmemPerm with ⟨permutation, hpermutation, rfl⟩
  exact ⟨representative, hrepresentative,
    permutation, hpermutation, rfl⟩

end

end Erdos85

#print axioms Erdos85.sevenHighT0CanonicalEmptyAdmissible_exists_representative_permutation
