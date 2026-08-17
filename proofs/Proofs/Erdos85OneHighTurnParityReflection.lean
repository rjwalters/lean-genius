import Proofs.Erdos85OneHighTurnParityInventory

/-! # Soundness bridge for the compact saturated odd-turn evaluator -/

namespace Erdos85

/-- A pointwise compatible choice remains compatible when its option list at
one coordinate is replaced by the singleton containing the choice already
made there. -/
theorem oneHighChoicesCompatible_set_singleton_of_getElem?_eq_some
    {A : Type*} {choiceLists : List (List A)} {choices : List A}
    (h : OneHighChoicesCompatible choiceLists choices)
    {i : Nat} {choice : A} (hget : choices[i]? = some choice) :
    OneHighChoicesCompatible (choiceLists.set i [choice]) choices := by
  induction choiceLists generalizing choices i with
  | nil =>
      cases choices with
      | nil => simp at hget
      | cons choice suffix => exact False.elim h
  | cons options rest ih =>
      cases choices with
      | nil => simp [OneHighChoicesCompatible] at h
      | cons chosen suffix =>
          simp only [OneHighChoicesCompatible] at h
          rcases h with ⟨hchosen, hsuffix⟩
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
              subst choice
              exact ⟨by simp, hsuffix⟩
          | succ i =>
              simp only [List.getElem?_cons_succ] at hget
              simp [List.set, OneHighChoicesCompatible, hchosen,
                ih hsuffix hget]

/-- Reading one coordinate of a compatible choice produces a member of the
corresponding option list. -/
theorem mem_getElem!_of_oneHighChoicesCompatible_getElem?_eq_some
    {A : Type*} [Inhabited A]
    {choiceLists : List (List A)} {choices : List A}
    (h : OneHighChoicesCompatible choiceLists choices)
    {i : Nat} {choice : A} (hget : choices[i]? = some choice) :
    choice ∈ choiceLists[i]! := by
  induction choiceLists generalizing choices i with
  | nil =>
      cases choices with
      | nil => simp at hget
      | cons choice suffix => exact False.elim h
  | cons options rest ih =>
      cases choices with
      | nil => simp [OneHighChoicesCompatible] at h
      | cons chosen suffix =>
          simp only [OneHighChoicesCompatible] at h
          rcases h with ⟨hchosen, hsuffix⟩
          cases i with
          | zero =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
              simpa [hget] using hchosen
          | succ i =>
              simp only [List.getElem?_cons_succ] at hget
              simpa using ih hsuffix hget

theorem left_mem_canonicalPair_endpoints (a b : Fin 8) :
    a ∈ [oneHighCanonicalLabelPair a b |>.1,
      oneHighCanonicalLabelPair a b |>.2] := by
  by_cases hab : a ≤ b
  · simp [oneHighCanonicalLabelPair, hab]
  · have hba : b ≤ a := le_of_not_ge hab
    simp [oneHighCanonicalLabelPair, hba]

theorem right_mem_canonicalPair_endpoints (a b : Fin 8) :
    b ∈ [oneHighCanonicalLabelPair a b |>.1,
      oneHighCanonicalLabelPair a b |>.2] := by
  by_cases hab : a ≤ b
  · simp [oneHighCanonicalLabelPair, hab]
  · have hba : b ≤ a := le_of_not_ge hab
    simp [oneHighCanonicalLabelPair, hba]

/-- The semantic full-refinement witness is accepted by the compact fixed-row
parity evaluator.  This is the sound direction used by the graph terminal. -/
theorem oneHighTableHasSaturatedOddThreePairTurnByParity_of_refinement
    {profile : Nat} {table : OneHighMissTable}
    {refinement : List (List OneHighLabelPair)}
    (hrefinement : refinement ∈
      oneHighPairingRefinements profile (oneHighTableRestrict table))
    (hturn : oneHighRefinementHasSaturatedOddThreePairTurn refinement = true) :
    oneHighTableHasSaturatedOddThreePairTurnByParity profile table = true := by
  rw [oneHighRefinementHasSaturatedOddThreePairTurn,
    decide_eq_true_eq] at hturn
  rcases hturn with ⟨source, a, b, c, row, hget, hperm,
    hsa, hsb, hsc, hab, hbc, hac, hoddAB, hoddBC⟩
  let choices := List.ofFn fun current : Fin 8 =>
    oneHighCompatibleSourcePairings profile (oneHighTableRestrict table) current
  have hcompatible : OneHighChoicesCompatible choices refinement := by
    exact (oneHighPairingRefinements_mem_iff profile
      (oneHighTableRestrict table) refinement).1
      hrefinement
  have hrowMemRaw : row ∈ choices[source.val]! :=
    mem_getElem!_of_oneHighChoicesCompatible_getElem?_eq_some
      hcompatible hget
  have hrowMem : row ∈
      oneHighCompatibleSourcePairings profile
        (oneHighTableRestrict table) source := by
    fin_cases source <;> simpa [choices] using hrowMemRaw
  have habRow : oneHighCanonicalLabelPair a b ∈ row := by
    rw [hperm.mem_iff]
    simp
  have hbcRow : oneHighCanonicalLabelPair b c ∈ row := by
    rw [hperm.mem_iff]
    simp
  let labels := (row.flatMap fun pair => [pair.1, pair.2]).eraseDups
  have haLabels : a ∈ labels := by
    simp only [labels, List.mem_eraseDups, List.mem_flatMap]
    exact ⟨oneHighCanonicalLabelPair a b, habRow,
      left_mem_canonicalPair_endpoints a b⟩
  have hbLabels : b ∈ labels := by
    simp only [labels, List.mem_eraseDups, List.mem_flatMap]
    exact ⟨oneHighCanonicalLabelPair a b, habRow,
      right_mem_canonicalPair_endpoints a b⟩
  have hcLabels : c ∈ labels := by
    simp only [labels, List.mem_eraseDups, List.mem_flatMap]
    exact ⟨oneHighCanonicalLabelPair b c, hbcRow,
      right_mem_canonicalPair_endpoints b c⟩
  have htriple : (a, b, c) ∈ oneHighSaturatedTurnRowTriples source row := by
    simp only [oneHighSaturatedTurnRowTriples, List.mem_flatMap,
      List.mem_filterMap]
    exact ⟨a, haLabels, b, hbLabels, c, hcLabels,
      by simp [hperm, hsa, hsb, hsc, hab, hbc, hac]⟩
  have hfixed : OneHighChoicesCompatible
      (choices.set source.val [row]) refinement :=
    oneHighChoicesCompatible_set_singleton_of_getElem?_eq_some
      hcompatible hget
  have hmaskMem : oneHighPairingRefinementParityMask refinement ∈
      oneHighPairingParityStatesWithSourceRowChoices choices source row := by
    rw [oneHighPairingParityStatesWithSourceRowChoices,
      mem_oneHighChooseEachParityStates_iff]
    exact ⟨refinement,
      (oneHighChooseEach_mem_iff _ _).2 hfixed, rfl⟩
  have hmaskAB : oneHighParityMaskOdd
      (oneHighPairingRefinementParityMask refinement) a b = true := by
    rw [oneHighParityMaskOdd_refinement]
    simp [oneHighMultiplicityOdd, Nat.odd_iff.mp hoddAB]
  have hmaskBC : oneHighParityMaskOdd
      (oneHighPairingRefinementParityMask refinement) b c = true := by
    rw [oneHighParityMaskOdd_refinement]
    simp [oneHighMultiplicityOdd, Nat.odd_iff.mp hoddBC]
  have htriplesNe : oneHighSaturatedTurnRowTriples source row ≠ [] :=
    List.ne_nil_of_mem htriple
  have hrowFilteredRaw : row ∈ choices[source.val]!.filter fun candidate =>
      !(oneHighSaturatedTurnRowTriples source candidate).isEmpty := by
    rw [List.mem_filter]
    exact ⟨hrowMemRaw, by simpa using htriplesNe⟩
  rw [oneHighTableHasSaturatedOddThreePairTurnByParity]
  change (List.ofFn fun source : Fin 8 => source).any (fun source =>
    let rows := choices[source.val]!.filter fun candidate =>
      !(oneHighSaturatedTurnRowTriples source candidate).isEmpty
    !rows.isEmpty && rows.any fun row =>
      let triples := oneHighSaturatedTurnRowTriples source row
      (oneHighPairingParityStatesWithSourceRowChoices
        choices source row).any fun mask =>
        triples.any fun triple =>
          oneHighParityMaskOdd mask triple.1 triple.2.1 &&
            oneHighParityMaskOdd mask triple.2.1 triple.2.2) = true
  rw [List.any_eq_true]
  refine ⟨source, ?_, ?_⟩
  · fin_cases source <;> simp
  rw [Bool.and_eq_true]
  constructor
  · cases hrows : choices[source.val]!.filter fun candidate =>
        !(oneHighSaturatedTurnRowTriples source candidate).isEmpty with
    | nil =>
        rw [hrows] at hrowFilteredRaw
        simp at hrowFilteredRaw
    | cons head tail => simp
  · rw [List.any_eq_true]
    refine ⟨row, ?_, ?_⟩
    · exact hrowFilteredRaw
    · rw [List.any_eq_true]
      refine ⟨oneHighPairingRefinementParityMask refinement, ?_, ?_⟩
      · exact hmaskMem
      · rw [List.any_eq_true]
        exact ⟨(a, b, c), htriple, by simp [hmaskAB, hmaskBC]⟩

/-- Sound finite-inventory consumer: a capacity table carrying the concrete
odd-turn refinement lies in the certified 9,707-row inventory. -/
theorem mem_oneHighSaturatedOddTurnParityInventoryTables_of_refinement
    {profile : Fin 5} {table : OneHighMissTable}
    (hcapacity : table ∈ oneHighCapacityInventoryTables profile)
    {refinement : List (List OneHighLabelPair)}
    (hrefinement : refinement ∈
      oneHighPairingRefinements profile.val (oneHighTableRestrict table))
    (hturn : oneHighRefinementHasSaturatedOddThreePairTurn refinement = true) :
    table ∈ oneHighSaturatedOddTurnParityInventoryTables profile := by
  rw [oneHighSaturatedOddTurnParityInventoryTables, List.mem_filter]
  exact ⟨hcapacity,
    oneHighTableHasSaturatedOddThreePairTurnByParity_of_refinement
      hrefinement hturn⟩

end Erdos85
