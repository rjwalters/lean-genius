import Proofs.Erdos85OneHighStructuralTerminalInterface
import Proofs.Erdos85OneHighExchangedMissCounting
import Proofs.Erdos85OneHighSameMissCountingBridge
import Proofs.Erdos85OneHighSameMissParityConsumer
import Proofs.Erdos85QuotientCutParity
import Proofs.Erdos85OneHighRepeatedSourceCapacity

/-! # Reduction of the one-high all-even terminal -/

namespace Erdos85

noncomputable section

/-- If every exchanged key has even multiplicity, then the total number of
nonconstant matching edges is even. -/
theorem even_nonconstantMatchingEdgeSources_of_all_exchanged_even
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L)
    (heven : ∀ key ∈ exchangedMissPairKeys L,
      Even (exchangedMissPairMultiplicity mate label key)) :
    Even (nonconstantMatchingEdgeSources mate label).card := by
  rw [← sum_exchangedMissPairMultiplicity_over_keys mate label]
  exact Finset.even_sum _ fun key hkey => heven key hkey

/-- An all-even exchanged multiset is either empty or contains two distinct
matching edges carrying the same genuine exchanged key. -/
theorem empty_or_repeated_exchangedPair_of_all_even
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L)
    (heven : ∀ key ∈ exchangedMissPairKeys L,
      Even (exchangedMissPairMultiplicity mate label key)) :
    nonconstantMatchingEdgeSources mate label = ∅ ∨
      ∃ key ∈ exchangedMissPairKeys L,
        ∃ x ∈ nonconstantMatchingEdgeSources mate label,
          ∃ y ∈ nonconstantMatchingEdgeSources mate label,
            x ≠ y ∧ exchangedMissPairKey mate label x = key ∧
              exchangedMissPairKey mate label y = key := by
  by_cases hempty : nonconstantMatchingEdgeSources mate label = ∅
  · exact Or.inl hempty
  · right
    obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    let key := exchangedMissPairKey mate label x
    have hkey : key ∈ exchangedMissPairKeys L := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        exchangedMissPairKey_lt_of_mem hx⟩
    have hxFiber : x ∈ (nonconstantMatchingEdgeSources mate label).filter
        fun z => exchangedMissPairKey mate label z = key :=
      Finset.mem_filter.mpr ⟨hx, rfl⟩
    have hpos : 0 < exchangedMissPairMultiplicity mate label key := by
      unfold exchangedMissPairMultiplicity
      exact Finset.card_pos.mpr ⟨x, hxFiber⟩
    have htwo : 1 < exchangedMissPairMultiplicity mate label key := by
      obtain ⟨k, hk⟩ := heven key hkey
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp htwo
    have haParts := Finset.mem_filter.mp ha
    have hbParts := Finset.mem_filter.mp hb
    exact ⟨key, hkey, a, haParts.1, b, hbParts.1, hab,
      haParts.2, hbParts.2⟩

/-- Graph-facing all-even dichotomy: either every internal edge has the same
miss at both endpoints, or two distinct global internal edges carry the same
unordered pair of canonical miss labels. -/
theorem oneHigh_globalSameMiss_or_repeated_exchangedPair_of_all_even
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (heven : ∀ key ∈ exchangedMissPairKeys (Fin 8),
      Even (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)) key)) :
    OneHighGlobalSameMiss G hfree v p.mate ∨
      ∃ key ∈ exchangedMissPairKeys (Fin 8),
        ∃ x ∈ nonconstantMatchingEdgeSources
          (oneHighGlobalInternalMate G hfree v)
          (fun z => p.branchLabel
            (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
              p.mate p.mate_adj z)),
        ∃ y ∈ nonconstantMatchingEdgeSources
          (oneHighGlobalInternalMate G hfree v)
          (fun z => p.branchLabel
            (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
              p.mate p.mate_adj z)),
          x ≠ y ∧
            exchangedMissPairKey (oneHighGlobalInternalMate G hfree v)
              (fun z => p.branchLabel
                (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
                  p.mate p.mate_adj z)) x = key ∧
            exchangedMissPairKey (oneHighGlobalInternalMate G hfree v)
              (fun z => p.branchLabel
                (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
                  p.mate p.mate_adj z)) y = key := by
  let mate := oneHighGlobalInternalMate G hfree v
  let rawLabel := oneHighGlobalMissLabel G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj
  let label := fun x => p.branchLabel (rawLabel x)
  obtain hempty | hrepeated :=
    empty_or_repeated_exchangedPair_of_all_even mate label heven
  · left
    apply (oneHigh_nonconstantSources_eq_empty_iff_globalSameMiss
      G hfree hv p.external_empty p.outer_degree p.mate p.mate_adj).mp
    simpa [mate, label, rawLabel, nonconstantMatchingEdgeSources] using hempty
  · exact Or.inr hrepeated

/-- Matching edges on which the two endpoint miss labels agree. -/
def constantMatchingEdgeSources
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [DecidableEq L] (mate : X → X) (label : X → L) : Finset X :=
  (matchingEdgeSources mate).filter fun x => label x = label (mate x)

theorem card_nonconstant_add_card_constantMatchingEdgeSources
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [DecidableEq L] (mate : X → X) (label : X → L) :
    (nonconstantMatchingEdgeSources mate label).card +
      (constantMatchingEdgeSources mate label).card =
        (matchingEdgeSources mate).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [nonconstantMatchingEdgeSources, constantMatchingEdgeSources,
      matchingEdgeSources, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and]
    by_cases hlabel : label x = label (mate x) <;> simp [hlabel]
  · rw [Finset.disjoint_left]
    intro x hxNon hxConst
    exact (Finset.mem_filter.mp hxNon).2.2
      (Finset.mem_filter.mp hxConst).2

/-- The raw one-high profile has exactly `16 - profile` internal matching
edges across its eight five-point branches. -/
theorem card_globalMatchingEdgeSources_eq_profile
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V}
    (p : OneHighRawV2Presentation G hfree v) :
    (matchingEdgeSources (oneHighGlobalInternalMate G hfree v)).card =
      16 - p.profile := by
  have hcard := card_oneHighAllMatchedVertices_eq_profile
    G v p.branchLabel p.profile p.profile_le p.matched_count
  have htwice := two_mul_matchingEdgeSources_card
    (oneHighGlobalInternalMate G hfree v)
    (oneHighGlobalInternalMate_involutive G hfree v)
    (oneHighGlobalInternalMate_ne G hfree v)
  rw [hcard] at htwice
  omega

private theorem even_sixteen_sub_iff (a : Nat) (ha : a ≤ 4) :
    Even (16 - a) ↔ Even a := by
  interval_cases a <;> decide

/-- A symmetric admissible miss table whose six relevant entries in every
row are all even can only have an even family profile. -/
theorem even_profile_of_admissible_all_relevant_even
    {profile : Nat} (hprofile : profile ≤ 4) (table : OneHighMissTable)
    (hadm : OneHighFamilyV2Admissible profile table)
    (heven : ∀ c : Fin 8,
      ∀ j ∈ ((Finset.univ.erase c).erase (oneHighStandardMate c)),
        Even (table c.val j.val)) :
    Even profile := by
  let F : Fin 8 → Fin 8 → Nat := fun c j =>
    if j ∈ ((Finset.univ.erase c).erase (oneHighStandardMate c))
      then table c.val j.val else 0
  let H : Fin 8 → Fin 8 → Nat := fun c j => F c j / 2
  have hF_even (c j : Fin 8) : Even (F c j) := by
    simp only [F]
    split
    · exact heven c j ‹_›
    · exact Even.zero
  have hF_eq (c j : Fin 8) : F c j = 2 * H c j := by
    obtain ⟨k, hk⟩ := hF_even c j
    simp only [H]
    omega
  have hF_symm (c j : Fin 8) : F c j = F j c := by
    by_cases hcj : c = j
    · subst j
      rfl
    by_cases hjm : j = oneHighStandardMate c
    · subst j
      have hcm : c = oneHighStandardMate (oneHighStandardMate c) := by
        rw [oneHighStandardMate_involutive]
      simp only [F, Finset.mem_erase, Finset.mem_univ, and_true]
      rw [if_neg (fun h => h.1 rfl), if_neg (fun h => h.1 hcm)]
    · have hjc : j ≠ c := Ne.symm hcj
      have hcm : c ≠ oneHighStandardMate j := by
        intro h
        apply hjm
        rw [h, oneHighStandardMate_involutive]
      simp only [F, Finset.mem_erase, Finset.mem_univ, and_true]
      rw [if_pos ⟨hjm, hjc⟩, if_pos ⟨hcm, hcj⟩]
      exact hadm.symm c j hjc hjm
  have hH_symm (c j : Fin 8) : H c j = H j c := by
    simp only [H, hF_symm]
  have hHtotal : Even (∑ c : Fin 8, ∑ j : Fin 8, H c j) := by
    apply even_principal_sum_of_pair_even Finset.univ H
    · intro c _
      simp [H, F]
    · intro c _ j _ hcj
      rw [hH_symm c j]
      exact Even.add_self _
  have htotalF : (∑ c : Fin 8, ∑ j : Fin 8, F c j) =
      32 - 2 * profile := by
    calc
      (∑ c : Fin 8, ∑ j : Fin 8, F c j) =
          ∑ c : Fin 8, 2 * oneHighFamilyInternalEdges profile c := by
        apply Finset.sum_congr rfl
        intro c _
        rw [← hadm.row_sum c]
        simp only [F]
        rw [← Finset.sum_subset (Finset.subset_univ _) (by
          intro j _ hj
          rw [if_neg hj])]
        apply Finset.sum_congr rfl
        intro j hj
        rw [if_pos hj]
      _ = 32 - 2 * profile :=
        sum_two_mul_oneHighFamilyInternalEdges profile hprofile
  have htotalFH : (∑ c : Fin 8, ∑ j : Fin 8, F c j) =
      2 * (∑ c : Fin 8, ∑ j : Fin 8, H c j) := by
    simp_rw [hF_eq, Finset.mul_sum]
  have hhalf : (∑ c : Fin 8, ∑ j : Fin 8, H c j) = 16 - profile := by
    rw [htotalF] at htotalFH
    omega
  rw [hhalf] at hHtotal
  exact (even_sixteen_sub_iff profile hprofile).mp hHtotal

/-- Dividing an all-even admissible table by two gives a symmetric weighted
graph whose row degree is exactly the profile internal-edge count (`1` or
`2`).  This is the residual object in the surviving even profiles. -/
theorem halfTable_row_sum_eq_familyInternalEdges
    {profile : Nat} (table : OneHighMissTable)
    (hadm : OneHighFamilyV2Admissible profile table)
    (heven : ∀ c : Fin 8,
      ∀ j ∈ ((Finset.univ.erase c).erase (oneHighStandardMate c)),
        Even (table c.val j.val))
    (c : Fin 8) :
    (∑ j ∈ ((Finset.univ.erase c).erase (oneHighStandardMate c)),
      table c.val j.val / 2) = oneHighFamilyInternalEdges profile c := by
  have hdouble : (∑ j ∈ ((Finset.univ.erase c).erase
      (oneHighStandardMate c)), table c.val j.val) =
      2 * (∑ j ∈ ((Finset.univ.erase c).erase
        (oneHighStandardMate c)), table c.val j.val / 2) := by
    calc
      (∑ j ∈ ((Finset.univ.erase c).erase (oneHighStandardMate c)),
          table c.val j.val) =
          ∑ j ∈ ((Finset.univ.erase c).erase (oneHighStandardMate c)),
            2 * (table c.val j.val / 2) := by
        apply Finset.sum_congr rfl
        intro j hj
        obtain ⟨k, hk⟩ := heven c j hj
        omega
      _ = 2 * (∑ j ∈ ((Finset.univ.erase c).erase
          (oneHighStandardMate c)), table c.val j.val / 2) := by
        rw [Finset.mul_sum]
  rw [hadm.row_sum c] at hdouble
  omega

/-- Consequently, genuine global same-miss behavior is possible only in the
even profiles `0`, `2`, and `4`. -/
theorem even_profile_of_oneHighGlobalSameMiss
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (hsame : OneHighGlobalSameMiss G hfree v p.mate) :
    Even p.profile := by
  let E := oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel
  let R := oneHighRelabeledLeafGraph G v E
  let table := oneHighFamilyGraphTable R p.profile
  have hadm : OneHighFamilyV2Admissible p.profile table := by
    simpa [E, R, table] using p.graphTable_admissible G hfree hv
  apply even_profile_of_admissible_all_relevant_even
    p.profile_le table hadm
  intro c j hj
  let s := p.branchLabel.symm c
  let u := p.branchLabel.symm j
  have hjm : j ≠ oneHighStandardMate c :=
    (Finset.mem_erase.mp hj).1
  have hjc : j ≠ c :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
  have hus : u ≠ s := by
    intro h
    apply hjc
    simpa [s, u] using congrArg p.branchLabel h
  have hum : u ≠ p.mate s := by
    intro h
    apply hjm
    calc
      j = p.branchLabel u := by simp [u]
      _ = p.branchLabel (p.mate s) := by rw [h]
      _ = oneHighStandardMate (p.branchLabel s) := p.branch_mate s
      _ = oneHighStandardMate c := by simp [s]
  have hcount : Even (highBranchMissCount G v s u) := by
    apply even_highBranchMissCount_of_sameMiss G hfree (d := 7)
      (by simpa using hv) p.external_empty p.mate p.mate_adj p.outer_degree
      (internalEdge_sameMiss_of_globalSameMiss G hfree v p.mate hsame)
    exact Finset.mem_erase.mpr ⟨hum, Finset.mem_erase.mpr ⟨hus, by simp⟩⟩
  have htable := oneHighFamilyGraphTable_eq_highBranchMissCount
    G hfree v p.mate p.branchLabel p.branch_mate p.leafLabel p.profile
      p.constraints s u hus hum
  change Even (table c.val j.val)
  have htable' : table c.val j.val = highBranchMissCount G v s u := by
    simpa [table, R, E, s, u] using htable
  rw [htable']
  exact hcount

/-- In the odd profiles (`1` and `3`), the all-even sector necessarily lies
in the repeated-exchanged-pair branch; global same-miss is impossible. -/
theorem oneHigh_repeated_exchangedPair_of_all_even_of_profile_odd
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (hprofile : Odd p.profile)
    (heven : ∀ key ∈ exchangedMissPairKeys (Fin 8),
      Even (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)) key)) :
    ∃ key ∈ exchangedMissPairKeys (Fin 8),
      ∃ x ∈ nonconstantMatchingEdgeSources
        (oneHighGlobalInternalMate G hfree v)
        (fun z => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj z)),
      ∃ y ∈ nonconstantMatchingEdgeSources
        (oneHighGlobalInternalMate G hfree v)
        (fun z => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj z)),
        x ≠ y ∧
          exchangedMissPairKey (oneHighGlobalInternalMate G hfree v)
            (fun z => p.branchLabel
              (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
                p.mate p.mate_adj z)) x = key ∧
          exchangedMissPairKey (oneHighGlobalInternalMate G hfree v)
            (fun z => p.branchLabel
              (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
                p.mate p.mate_adj z)) y = key := by
  rcases oneHigh_globalSameMiss_or_repeated_exchangedPair_of_all_even
      G hfree hv p heven with hsame | hrepeated
  · exact ((Nat.not_even_iff_odd.mpr hprofile)
      (even_profile_of_oneHighGlobalSameMiss G hfree hv p hsame)).elim
  · exact hrepeated

/-- Pinned repeated-pair residual for the odd all-even profiles.  Equal
owners are automatically saturated two-edge branches; the other cases are
an exact mate-owner collision or genuinely separated owners. -/
structure OneHighOddProfileRepeatedPairResidual
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) where
  key : Fin 8 × Fin 8
  key_mem : key ∈ exchangedMissPairKeys (Fin 8)
  x : OneHighAllMatchedVertices G v
  y : OneHighAllMatchedVertices G v
  x_mem : x ∈ nonconstantMatchingEdgeSources
    (oneHighGlobalInternalMate G hfree v)
    (fun z => p.branchLabel
      (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
        p.mate p.mate_adj z))
  y_mem : y ∈ nonconstantMatchingEdgeSources
    (oneHighGlobalInternalMate G hfree v)
    (fun z => p.branchLabel
      (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
        p.mate p.mate_adj z))
  x_ne_y : x ≠ y
  x_key : exchangedMissPairKey (oneHighGlobalInternalMate G hfree v)
    (fun z => p.branchLabel
      (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
        p.mate p.mate_adj z)) x = key
  y_key : exchangedMissPairKey (oneHighGlobalInternalMate G hfree v)
    (fun z => p.branchLabel
      (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
        p.mate p.mate_adj z)) y = key
  owner_sector :
    (x.1 = y.1 ∧
      oneHighFamilyInternalEdges p.profile (p.branchLabel x.1) = 2) ∨
    x.1 = p.mate y.1 ∨
    (x.1 ≠ y.1 ∧ x.1 ≠ p.mate y.1)

theorem oneHigh_oddProfileRepeatedPairResidual_of_all_even
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) (hprofile : Odd p.profile)
    (heven : ∀ key ∈ exchangedMissPairKeys (Fin 8),
      Even (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)) key)) :
    Nonempty (OneHighOddProfileRepeatedPairResidual G hfree hv p) := by
  obtain ⟨key, hkey, x, hx, y, hy, hxy, hxkey, hykey⟩ :=
    oneHigh_repeated_exchangedPair_of_all_even_of_profile_odd
      G hfree hv p hprofile heven
  refine ⟨⟨key, hkey, x, y, hx, hy, hxy, hxkey, hykey, ?_⟩⟩
  by_cases howner : x.1 = y.1
  · exact Or.inl ⟨howner,
      oneHighFamilyInternalEdges_eq_two_of_distinct_sources_sameOwner
        G hfree hv p hx hy hxy howner⟩
  by_cases hmateOwner : x.1 = p.mate y.1
  · exact Or.inr (Or.inl hmateOwner)
  · exact Or.inr (Or.inr ⟨howner, hmateOwner⟩)

/-- Exact all-even invariant: same-miss internal edges have the same parity
as the family profile.  Thus the five terminal profiles require respectively
an even, odd, even, odd, and even same-miss count. -/
theorem even_constantMatchingEdgeSources_iff_profile_even_of_all_exchanged_even
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (heven : ∀ key ∈ exchangedMissPairKeys (Fin 8),
      Even (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x)) key)) :
    Even (constantMatchingEdgeSources
      (oneHighGlobalInternalMate G hfree v)
      (fun x => p.branchLabel
        (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
          p.mate p.mate_adj x))).card ↔ Even p.profile := by
  let mate := oneHighGlobalInternalMate G hfree v
  let label := fun x => p.branchLabel
    (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
      p.mate p.mate_adj x)
  have hnon : Even (nonconstantMatchingEdgeSources mate label).card :=
    even_nonconstantMatchingEdgeSources_of_all_exchanged_even mate label heven
  have hsum := card_nonconstant_add_card_constantMatchingEdgeSources mate label
  have htotal := card_globalMatchingEdgeSources_eq_profile G hfree p
  dsimp only [mate] at hsum htotal
  rw [htotal] at hsum
  constructor
  · intro hconst
    apply (even_sixteen_sub_iff p.profile p.profile_le).mp
    rw [← hsum]
    exact hnon.add hconst
  · intro hprofile
    have htotalEven : Even (16 - p.profile) :=
      (even_sixteen_sub_iff p.profile p.profile_le).mpr hprofile
    rw [← hsum, Nat.even_add] at htotalEven
    exact htotalEven.mp hnon

/-- The all-even terminal is reduced to the graph-side assertion that the
global nonconstant matching-edge count is odd. -/
theorem oneHighAllEvenSectorExcluded_of_global_nonconstant_odd
    (hodd : ∀ (G : SimpleGraph (Fin 49)) (_ : DecidableRel G.Adj)
      (_ : DecidableRel (antipodalGraph G).Adj)
      (_ : DecidableRel (triangleFreeEdgeGraph G).Adj),
      (hfree : ¬ containsC4 (Fin 49) G) →
      (hmin : ∀ x : Fin 49, 7 ≤ G.degree x) →
      (hHigh : (orderFortyNineHighVertices G).card = 1) →
      ∀ {v : Fin 49} (hv : G.degree v = 8)
        (p : OneHighRawV2Presentation G hfree v),
        Odd (nonconstantMatchingEdgeSources
          (oneHighGlobalInternalMate G hfree v)
          (fun x => p.branchLabel
            (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
              p.mate p.mate_adj x))).card) :
    OneHighAllEvenSectorExcluded := by
  intro G _ _ _ hfree hmin hHigh v hv p
  dsimp only
  intro heven
  let mate := oneHighGlobalInternalMate G hfree v
  let label := fun x => p.branchLabel
    (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
      p.mate p.mate_adj x)
  have hcardEven : Even (nonconstantMatchingEdgeSources mate label).card :=
    even_nonconstantMatchingEdgeSources_of_all_exchanged_even mate label heven
  have hcardOdd : Odd (nonconstantMatchingEdgeSources mate label).card :=
    hodd G inferInstance inferInstance inferInstance hfree hmin hHigh hv p
  exact (Nat.not_even_iff_odd.mpr hcardOdd) hcardEven

end

end Erdos85
