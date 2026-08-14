import Proofs.Erdos85OneHighV2OrbitInvariants
import Proofs.Erdos85OneHighV2TableAgree
import Proofs.Erdos85OneHighV2OrbitExclusion

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
abbrev OneHighFiniteMissTable := OneHighRelevantPair → Fin 5

/-- Equality on precisely the 24 coordinates represented by an artifact
table. -/
def OneHighRelevantAgreement
    (left right : OneHighMissTable) : Prop :=
  ∀ pair : OneHighRelevantPair,
    left pair.1.1.val pair.1.2.val = right pair.1.1.val pair.1.2.val

theorem oneHighRelevantPair_mem_tablePairs (pair : OneHighRelevantPair) :
    (pair.1.1.val, pair.1.2.val) ∈ oneHighFamilyTablePairs := by
  native_decide +revert

/-- The function-indexed finite agreement and the generator-audited list
agreement are the same 24-coordinate relation. -/
theorem oneHighRelevantAgreement_iff_tableRelevantAgree
    (left right : OneHighMissTable) :
    OneHighRelevantAgreement left right ↔
      OneHighTableRelevantAgree left right := by
  constructor
  · intro h pair hmem
    have hp := oneHighFamilyTablePairs_mem_bounds hmem
    let c : Fin 8 := ⟨pair.1, hp.1⟩
    let j : Fin 8 := ⟨pair.2, hp.2.1⟩
    apply h ⟨(c, j), hp.2.2.1, ?_⟩
    intro heq
    apply hp.2.2.2
    have hval := congrArg Fin.val heq
    rw [oneHighStandardMate_val_eq_xor] at hval
    exact hval
  · intro h pair
    exact h _ (oneHighRelevantPair_mem_tablePairs pair)

/-- Interpret a finite upper-triangular table as the sparse total function
used by certificate files.  Reverse relevant coordinates are mirrored;
irrelevant coordinates are zero. -/
def OneHighFiniteMissTable.toMissTable
    (table : OneHighFiniteMissTable) : OneHighMissTable := fun c j =>
  if hc : c < 8 then
    if hj : j < 8 then
      let cf : Fin 8 := ⟨c, hc⟩
      let jf : Fin 8 := ⟨j, hj⟩
      if hlt : cf < jf then
        if hnm : jf ≠ oneHighStandardMate cf then
          table ⟨(cf, jf), hlt, hnm⟩
        else 0
      else if hgt : jf < cf then
        if hnm : cf ≠ oneHighStandardMate jf then
          table ⟨(jf, cf), hgt, hnm⟩
        else 0
      else 0
    else 0
  else 0

@[simp] theorem OneHighFiniteMissTable.toMissTable_relevant
    (table : OneHighFiniteMissTable) (pair : OneHighRelevantPair) :
    table.toMissTable pair.1.1.val pair.1.2.val = table pair := by
  simp [OneHighFiniteMissTable.toMissTable, pair.2.1, pair.2.2]

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

theorem OneHighFamilyV2Admissible.agrees_toFinite_toMissTable
    {profile : Nat} {table : OneHighMissTable}
    (h : OneHighFamilyV2Admissible profile table) :
    OneHighRelevantAgreement table h.toFinite.toMissTable := by
  intro pair
  simp

/-- A specification-level exhaustive finite cover.  It is intentionally not
evaluated: the verified constrained enumerator will replace this enormous
`5^24` universe by the 13,541 CP4 representatives, while preserving this
coverage theorem. -/
noncomputable def oneHighAllFiniteMissTables : List OneHighMissTable :=
  ((Finset.univ : Finset OneHighFiniteMissTable).toList.map
    OneHighFiniteMissTable.toMissTable)

theorem OneHighFamilyV2Admissible.exists_mem_allFiniteMissTables_agrees
    {profile : Nat} {table : OneHighMissTable}
    (h : OneHighFamilyV2Admissible profile table) :
    ∃ stored ∈ oneHighAllFiniteMissTables,
      OneHighRelevantAgreement table stored := by
  refine ⟨h.toFinite.toMissTable, ?_,
    h.agrees_toFinite_toMissTable⟩
  simp [oneHighAllFiniteMissTables]

/-- The specification-level `5^24` list is already a formally complete raw
orbit cover.  The constrained enumerator and CP4 quotient are therefore
optimisations of a proved finite cover, rather than additional graph theory. -/
theorem oneHighRawV2OrbitCover_allFinite :
    OneHighRawV2OrbitCover (fun _ => oneHighAllFiniteMissTables) := by
  intro G _ _ _ hfree hmin hHigh
  have hnonempty : (orderFortyNineHighVertices G).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨v, hvMem⟩ := hnonempty
  have hv : G.degree v = 8 := by
    simpa [orderFortyNineHighVertices] using hvMem
  obtain ⟨p⟩ := orderFortyNine_exists_rawOneHighPresentationData
    G hfree hmin (Fintype.card_fin 49) hHigh hv
  let E := oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel
  let R := oneHighRelabeledLeafGraph G v E
  have hadmissible : OneHighFamilyV2Admissible p.profile
      (oneHighFamilyGraphTable R p.profile) :=
    p.graphTable_admissible G hfree hv
  obtain ⟨stored, hmem, hagree⟩ :=
    hadmissible.exists_mem_allFiniteMissTables_agrees
  refine ⟨v, hv, p, stored, hmem, ?_⟩
  exact (oneHighRelevantAgreement_iff_tableRelevantAgree _ _).mp hagree

/-- Certificate-only endpoint after the graph and finite-coverage arguments:
checked UNSAT evidence for the exhaustive finite tables closes h=1. -/
theorem orderFortyNineStratumExcluded_one_of_allFiniteChecked
    (hchecked : ∀ (profile : Fin 5) table,
      table ∈ oneHighAllFiniteMissTables →
        OneHighFamilyV2CheckedUnsat profile.val table) :
    OrderFortyNineStratumExcluded 1 :=
  orderFortyNineStratumExcluded_one_of_rawV2OrbitCover
    oneHighRawV2OrbitCover_allFinite (fun profile table hmem =>
      hchecked profile table hmem)

end Erdos85
