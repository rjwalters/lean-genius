import Proofs.Erdos85OneHighV2OrbitInvariants

/-! # Finite representation of the 24 relevant one-high miss entries -/

namespace Erdos85

/-- An upper-triangular, non-mate pair of the eight one-high branches. -/
abbrev OneHighRelevantPair :=
  {p : Fin 8 × Fin 8 // p.1 < p.2 ∧
    p.2 ≠ oneHighStandardMate p.1}

theorem oneHighRelevantPair_card : Fintype.card OneHighRelevantPair = 24 := by
  native_decide

/-- Every relevant miss count is at most four, so an admissible table has a
canonical finite representation with 24 `Fin 5` coordinates. -/
def OneHighFiniteMissTable := OneHighRelevantPair → Fin 5

/-- Equality on precisely the 24 coordinates represented by an artifact
table. -/
def OneHighRelevantAgreement
    (left right : OneHighMissTable) : Prop :=
  ∀ pair : OneHighRelevantPair,
    left pair.1.1.val pair.1.2.val = right pair.1.1.val pair.1.2.val

theorem OneHighFamilyV2Admissible.entry_lt_five
    {profile : Nat} {table : OneHighMissTable}
    (h : OneHighFamilyV2Admissible profile table)
    (c j : Fin 8) (hcj : c ≠ j)
    (hjm : j ≠ oneHighStandardMate c) :
    table c.val j.val < 5 := by
  have hjmem : j ∈
      ((Finset.univ.erase c).erase (oneHighStandardMate c)) := by
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact ⟨hjm, hcj.symm⟩
  have hle : table c.val j.val ≤
      ∑ k ∈ ((Finset.univ.erase c).erase (oneHighStandardMate c)),
        table c.val k.val := by
    exact Finset.single_le_sum
      (s := ((Finset.univ.erase c).erase (oneHighStandardMate c)))
      (f := fun k : Fin 8 => table c.val k.val)
      (fun _ _ => Nat.zero_le _) hjmem
  rw [h.row_sum c] at hle
  unfold oneHighFamilyInternalEdges at hle
  split at hle <;> omega

/-- Restrict an admissible total table to exactly the coordinates consumed
by the orbit enumerator and exact-v2 generator. -/
def OneHighFamilyV2Admissible.toFinite
    {profile : Nat} {table : OneHighMissTable}
    (h : OneHighFamilyV2Admissible profile table) :
    OneHighFiniteMissTable := fun pair =>
  ⟨table pair.1.1.val pair.1.2.val,
    h.entry_lt_five pair.1.1 pair.1.2 (Fin.ne_of_lt pair.2.1)
      pair.2.2⟩

@[simp] theorem OneHighFamilyV2Admissible.toFinite_apply
    {profile : Nat} {table : OneHighMissTable}
    (h : OneHighFamilyV2Admissible profile table)
    (pair : OneHighRelevantPair) :
    h.toFinite pair = table pair.1.1.val pair.1.2.val := rfl

theorem OneHighFamilyV2Admissible.toFinite_eq_iff
    {profile : Nat} {left right : OneHighMissTable}
    (hl : OneHighFamilyV2Admissible profile left)
    (hr : OneHighFamilyV2Admissible profile right) :
    hl.toFinite = hr.toFinite ↔ OneHighRelevantAgreement left right := by
  constructor
  · intro heq pair
    have := congrFun heq pair
    exact congrArg Fin.val this
  · intro hagree
    funext pair
    apply Fin.ext
    exact hagree pair

end Erdos85
