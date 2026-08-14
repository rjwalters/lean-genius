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

theorem oneHighProfilePerm_comm_mate {profile : Nat}
    (σ : OneHighProfilePerm profile) (i : Fin 8) :
    σ.1 (oneHighStandardMate i) = oneHighStandardMate (σ.1 i) :=
  σ.2.1 i

theorem oneHighProfilePerm_internalEdges {profile : Nat}
    (σ : OneHighProfilePerm profile) (i : Fin 8) :
    oneHighFamilyInternalEdges profile (σ.1 i) =
      oneHighFamilyInternalEdges profile i :=
  σ.2.2 i

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
