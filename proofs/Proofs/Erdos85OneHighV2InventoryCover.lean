import Proofs.Erdos85OneHighV2Cp4Action
import Proofs.Erdos85OneHighV2EnumCompleteness
import Proofs.Erdos85OneHighV2CanonicalKey
import Proofs.Erdos85OneHighV2Inventory
import Proofs.Erdos85OneHighV2Enumerator
import Proofs.Erdos85OneHighV2InventoryOrbitCheck

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

theorem oneHighPrunedEnumRawKeySet_eq_inventoryOrbit (profile : Fin 5) :
    oneHighPrunedEnumRawKeySet profile.val =
      oneHighInventoryOrbitRawKeySet profile := by
  fin_cases profile
  · exact oneHighPrunedEnumRawKeySet_eq_inventoryOrbit_zero
  · exact oneHighPrunedEnumRawKeySet_eq_inventoryOrbit_one
  · exact oneHighPrunedEnumRawKeySet_eq_inventoryOrbit_two
  · exact oneHighPrunedEnumRawKeySet_eq_inventoryOrbit_three
  · exact oneHighPrunedEnumRawKeySet_eq_inventoryOrbit_four

theorem oneHighPrunedEnum_exists_inventoryOrbit
    (profile : Fin 5) (w : OneHighFiniteMissTable)
    (hw : w ∈ enumerateOneHighFiniteTables profile.val) :
    ∃ (stored : OneHighFiniteMissTable)
      (σ : OneHighProfilePerm profile.val),
      stored ∈ oneHighInventoryFiniteTables profile ∧
        oneHighNatKey (oneHighFiniteNatify w) =
          oneHighNatKey
            (oneHighNatPermute σ.1 (oneHighFiniteNatify stored)) := by
  have hleft : oneHighNatKey (oneHighFiniteNatify w) ∈
      oneHighPrunedEnumRawKeySet profile.val := by
    rw [oneHighPrunedEnumRawKeySet, oneHighAdjacentDedup_mem_iff]
    simp only [List.mem_mergeSort]
    exact List.mem_map.mpr ⟨w, hw, rfl⟩
  rw [oneHighPrunedEnumRawKeySet_eq_inventoryOrbit profile] at hleft
  rw [oneHighInventoryOrbitRawKeySet,
    oneHighAdjacentDedup_mem_iff] at hleft
  simp only [List.mem_mergeSort, List.mem_flatMap, Finset.mem_sort,
    Finset.mem_image, Finset.mem_univ, true_and] at hleft
  rcases hleft with ⟨stored, hstored, σ, hkey⟩
  exact ⟨stored, σ, hstored, hkey.symm⟩

/-- Once the executable comparison says every enumerated canonical key is in
the authoritative inventory, the inventory is a representative cover. -/
theorem oneHighFiniteRepresentativeCover_inventory_of_key_membership
    (hkeys : ∀ (profile : Fin 5) key,
      key ∈ oneHighEnumCanonicalKeys profile.val →
        key ∈ oneHighInventoryKeys profile) :
    OneHighFiniteRepresentativeCover oneHighInventoryTables := by
  intro profile table hadmissible
  let w := oneHighNatRestrict table
  have hwmem : w ∈ oneHighEnumFiniteTables profile.val :=
    hadmissible.natRestrict_mem_enum
  have hcanonicalMem : oneHighCanonicalKey profile.val w ∈
      oneHighInventoryKeys profile := by
    apply hkeys profile
    exact List.mem_map.mpr ⟨w, hwmem, rfl⟩
  rw [oneHighInventoryKeys] at hcanonicalMem
  rcases List.mem_map.mp hcanonicalMem with
    ⟨storedFinite, hstoredFinite, hstoredKey⟩
  obtain ⟨σ, hσ⟩ := oneHighCanonicalKey_exists profile.val w
  have hwBound : ∀ pair, oneHighNatPermute σ.1 w pair < 5 := by
    intro pair
    rw [oneHighNatPermute_natRestrict hadmissible σ]
    exact (hadmissible.permute σ).entry_lt_five pair.1.1 pair.1.2
      (Fin.ne_of_lt pair.2.1)
      pair.2.2
  have hstoredBound : ∀ pair, oneHighFiniteNatify storedFinite pair < 5 :=
    fun pair => (storedFinite pair).isLt
  have hfiniteEq : oneHighNatPermute σ.1 w =
      oneHighFiniteNatify storedFinite := by
    apply oneHighNatKey_inj hwBound hstoredBound
    exact hσ.symm.trans hstoredKey.symm
  obtain ⟨stored, hstoredMem, hstoredAgree⟩ :=
    oneHighInventoryFiniteTables_sound profile storedFinite hstoredFinite
  refine ⟨σ, stored, hstoredMem, ?_⟩
  rw [← oneHighRelevantAgreement_iff_tableRelevantAgree]
  intro pair
  have hvalues := congrFun
    ((oneHighNatPermute_natRestrict hadmissible σ).symm.trans hfiniteEq) pair
  have hagreeFinite :
      σ.permuteTable table pair.1.1.val pair.1.2.val =
        storedFinite.toMissTable pair.1.1.val pair.1.2.val := by
    simpa [w, oneHighNatRestrict, oneHighFiniteNatify] using hvalues
  exact hagreeFinite.trans (hstoredAgree pair)

end Erdos85
