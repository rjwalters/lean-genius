import Proofs.Erdos85OneHighV2Cp4Action
import Proofs.Erdos85OneHighV2EnumCompleteness
import Proofs.Erdos85OneHighV2Inventory

/-! # Connecting the executable CP4 classifier to the stored inventory -/

namespace Erdos85

private theorem listForall_of_mem {α : Type*} {p : α → Prop}
    {xs : List α} (h : xs.Forall p) {x : α} (hx : x ∈ xs) : p x := by
  exact (List.forall_iff_forall_mem.mp h) x hx

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

/-- The parsed authoritative rows are already in the `Fin 5` range on every
coordinate consumed by the generator. -/
theorem oneHighInventoryRows_relevant_lt_five :
    oneHighInventoryRows.Forall fun row =>
      ∀ pair : OneHighRelevantPair,
        oneHighInventoryRowTable row pair.1.1.val pair.1.2.val < 5 := by
  native_decide

/-- Membership in the finite inventory recovers the corresponding stored
total row, without losing any relevant value to the parser's `% 5`. -/
theorem oneHighInventoryFiniteTables_sound
    (profile : Fin 5) (w : OneHighFiniteMissTable)
    (hmem : w ∈ oneHighInventoryFiniteTables profile) :
    ∃ stored : OneHighMissTable,
      stored ∈ oneHighInventoryTables profile ∧
        OneHighRelevantAgreement w.toMissTable stored := by
  rw [oneHighInventoryFiniteTables] at hmem
  rcases List.mem_filterMap.mp hmem with ⟨row, hrow, hopt⟩
  split at hopt
  · simp only [Option.some.injEq] at hopt
    subst w
    refine ⟨oneHighInventoryRowTable row, ?_, ?_⟩
    · rw [oneHighInventoryTables]
      apply List.mem_filterMap.mpr
      exact ⟨row, hrow, by simp_all⟩
    · intro pair
      simp only [OneHighFiniteMissTable.toMissTable_relevant,
        oneHighInventoryRowFiniteTable]
      exact Nat.mod_eq_of_lt
        ((listForall_of_mem oneHighInventoryRows_relevant_lt_five hrow) pair)
  · simp at hopt

end Erdos85
