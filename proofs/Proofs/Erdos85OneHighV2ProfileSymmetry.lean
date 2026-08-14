import Proofs.Erdos85OneHighV2FiniteTable

/-! # Profile-preserving CP4 symmetries of one-high miss tables -/

namespace Erdos85

/-- The exact stabilizer used by `enumerate_h1_miss_tables.py`: a branch
permutation must commute with the four canonical mate pairs and preserve the
profile row target at every branch. -/
abbrev OneHighProfilePerm (profile : Nat) :=
  {σ : Equiv.Perm (Fin 8) //
    (∀ i, σ (oneHighStandardMate i) = oneHighStandardMate (σ i)) ∧
    (∀ i, oneHighFamilyInternalEdges profile (σ i) =
      oneHighFamilyInternalEdges profile i)}

/-- Identity is always a profile-preserving mate-pair symmetry. -/
def oneHighProfilePermId (profile : Nat) : OneHighProfilePerm profile :=
  ⟨1, by simp, by simp⟩

/-- Profile stabilizers are closed under composition. -/
def OneHighProfilePerm.comp {profile : Nat}
    (σ τ : OneHighProfilePerm profile) : OneHighProfilePerm profile := by
  refine ⟨σ.1 * τ.1, ?_, ?_⟩
  · intro i
    change σ.1 (τ.1 (oneHighStandardMate i)) =
      oneHighStandardMate (σ.1 (τ.1 i))
    rw [τ.2.1 i, σ.2.1 (τ.1 i)]
  · intro i
    change oneHighFamilyInternalEdges profile (σ.1 (τ.1 i)) = _
    rw [σ.2.2 (τ.1 i), τ.2.2 i]

/-- Profile stabilizers are closed under inverse. -/
def OneHighProfilePerm.inv {profile : Nat}
    (σ : OneHighProfilePerm profile) : OneHighProfilePerm profile := by
  refine ⟨σ.1.symm, ?_, ?_⟩
  · intro i
    apply σ.1.injective
    rw [σ.1.apply_symm_apply, σ.2.1]
    simp
  · intro i
    have h := σ.2.2 (σ.1.symm i)
    simpa using h.symm

theorem oneHighProfilePerm_comm_mate {profile : Nat}
    (σ : OneHighProfilePerm profile) (i : Fin 8) :
    σ.1 (oneHighStandardMate i) = oneHighStandardMate (σ.1 i) :=
  σ.2.1 i

theorem oneHighProfilePerm_internalEdges {profile : Nat}
    (σ : OneHighProfilePerm profile) (i : Fin 8) :
    oneHighFamilyInternalEdges profile (σ.1 i) =
      oneHighFamilyInternalEdges profile i :=
  σ.2.2 i

/-- Pull back a total miss table along a profile symmetry.  Coordinates
outside `Fin 8` remain irrelevant and are normalised to zero. -/
def OneHighProfilePerm.permuteTable {profile : Nat}
    (σ : OneHighProfilePerm profile) (table : OneHighMissTable) :
    OneHighMissTable := fun c j =>
  if hc : c < 8 then
    if hj : j < 8 then
      table (σ.1.symm ⟨c, hc⟩).val (σ.1.symm ⟨j, hj⟩).val
    else 0
  else 0

@[simp] theorem OneHighProfilePerm.permuteTable_apply
    {profile : Nat} (σ : OneHighProfilePerm profile)
    (table : OneHighMissTable) (c j : Fin 8) :
    σ.permuteTable table c.val j.val =
      table (σ.1.symm c).val (σ.1.symm j).val := by
  simp [OneHighProfilePerm.permuteTable]

/-- The finite orbit searched by the Python representative selector.  The
restriction discards coordinates the exact-v2 generator never reads. -/
noncomputable def oneHighProfileTableOrbit (profile : Nat)
    (table : OneHighMissTable) : List OneHighMissTable :=
  (Finset.univ : Finset (OneHighProfilePerm profile)).toList.map fun σ =>
    oneHighTableRestrict (σ.permuteTable table)

theorem oneHighProfileTableOrbit_nonempty (profile : Nat)
    (table : OneHighMissTable) :
    (oneHighProfileTableOrbit profile table).length ≠ 0 := by
  classical
  simp only [oneHighProfileTableOrbit, List.length_map,
    Finset.length_toList, Finset.card_univ]
  exact Nat.ne_of_gt
    (Fintype.card_pos_iff.mpr ⟨oneHighProfilePermId profile⟩)

/-- The five stabilizer orders independently reproduce the Python CP4
filter: BBBB, ABBB, AABB, AAAB, AAAA respectively. -/
theorem oneHighProfilePerm_card_zero :
    Fintype.card (OneHighProfilePerm 0) = 384 := by native_decide

theorem oneHighProfilePerm_card_one :
    Fintype.card (OneHighProfilePerm 1) = 48 := by native_decide

theorem oneHighProfilePerm_card_two :
    Fintype.card (OneHighProfilePerm 2) = 16 := by native_decide

theorem oneHighProfilePerm_card_three :
    Fintype.card (OneHighProfilePerm 3) = 12 := by native_decide

theorem oneHighProfilePerm_card_four :
    Fintype.card (OneHighProfilePerm 4) = 24 := by native_decide

end Erdos85
