import Proofs.Erdos85OneHighStructuralTerminalInterface
import Proofs.Erdos85OneHighExchangedMissCounting
import Proofs.Erdos85OneHighSameMissCountingBridge
import Proofs.Erdos85OneHighSameMissParityConsumer
import Proofs.Erdos85QuotientCutParity
import Proofs.Erdos85OneHighRepeatedSourceCapacity
import Proofs.Erdos85OneHighGraphPairingRefinement

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

/-- A reciprocal pair of concrete same-miss internal edges, represented by
one matched endpoint in each of the two source branches. -/
structure OneHighReciprocalSameMissEdges
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v) where
  s : {z : V // z ∈ G.neighborSet v}
  u : {z : V // z ∈ G.neighborSet v}
  s_label : p.branchLabel s = 0
  u_far : u ∈ ((Finset.univ.erase s).erase (p.mate s))
  x : OneHighMatchedBranchVertices G v s
  a : OneHighMatchedBranchVertices G v u
  x_misses_u : oneHighMatchedMissLabel G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj s x = u
  x_mate_misses_u : oneHighMatchedMissLabel G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj s
      (oneHighInternalMate G hfree v s x) = u
  a_misses_s : oneHighMatchedMissLabel G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj u a = s
  a_mate_misses_s : oneHighMatchedMissLabel G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj u
      (oneHighInternalMate G hfree v u a) = s
  x_to_u_zero : (G.neighborFinset x.1.1 ∩
    secondLayerBranch G v u).card = 0
  x_mate_to_u_zero :
    (G.neighborFinset (oneHighInternalMate G hfree v s x).1.1 ∩
      secondLayerBranch G v u).card = 0
  a_to_s_zero : (G.neighborFinset a.1.1 ∩
    secondLayerBranch G v s).card = 0
  a_mate_to_s_zero :
    (G.neighborFinset (oneHighInternalMate G hfree v u a).1.1 ∩
      secondLayerBranch G v s).card = 0

/-- Global same-miss behavior always contains a reciprocal pair of concrete
internal edges: an edge in branch `s` misses `u`, and an edge in branch `u`
misses `s`. -/
theorem exists_oneHighReciprocalSameMissEdges
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (hsame : OneHighGlobalSameMiss G hfree v p.mate) :
    Nonempty (OneHighReciprocalSameMissEdges G hfree hv p) := by
  let s := p.branchLabel.symm 0
  have hrow := p.sum_far_missCount G hfree hv s
  have hrowPos : 0 < ∑ u ∈ ((Finset.univ.erase s).erase (p.mate s)),
      highBranchMissCount G v s u := by
    rw [hrow]
    unfold oneHighFamilyInternalEdges
    split <;> omega
  obtain ⟨u, hu, hsuPos⟩ := Finset.sum_pos_iff.mp hrowPos
  have hus : s ∈ ((Finset.univ.erase u).erase (p.mate u)) := by
    have hum : u ≠ p.mate s := (Finset.mem_erase.mp hu).1
    have hus : u ≠ s :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hu).2).1
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_erase.mpr ⟨hus.symm, Finset.mem_univ _⟩⟩
    intro hsm
    apply hum
    exact (p.mate_involutive u).symm.trans (congrArg p.mate hsm).symm
  have husPos : 0 < highBranchMissCount G v u s := by
    simpa [p.missCount_comm G hfree v s u] using hsuPos
  have hxCard := card_oneHighMatchedMissLabelFiber_eq_highBranchMissCount
    G hfree hv p.external_empty p.outer_degree p.mate p.mate_adj s u hu
  have haCard := card_oneHighMatchedMissLabelFiber_eq_highBranchMissCount
    G hfree hv p.external_empty p.outer_degree p.mate p.mate_adj u s hus
  have hxNonempty : ((Finset.univ : Finset
      (OneHighMatchedBranchVertices G v s)).filter fun x =>
        oneHighMatchedMissLabel G hfree hv p.external_empty p.outer_degree
          p.mate p.mate_adj s x = u).Nonempty := by
    rw [← Finset.card_pos, hxCard]
    exact hsuPos
  have haNonempty : ((Finset.univ : Finset
      (OneHighMatchedBranchVertices G v u)).filter fun a =>
        oneHighMatchedMissLabel G hfree hv p.external_empty p.outer_degree
          p.mate p.mate_adj u a = s).Nonempty := by
    rw [← Finset.card_pos, haCard]
    exact husPos
  obtain ⟨x, hx⟩ := hxNonempty
  obtain ⟨a, ha⟩ := haNonempty
  have hxMiss := (Finset.mem_filter.mp hx).2
  have haMiss := (Finset.mem_filter.mp ha).2
  have hxSame := (oneHighGlobalMissLabel_eq_iff_sameMiss_at
    G hfree hv p.external_empty p.outer_degree p.mate p.mate_adj
      (⟨s, x⟩ : OneHighAllMatchedVertices G v)).mpr (hsame ⟨s, x⟩)
  have haSame := (oneHighGlobalMissLabel_eq_iff_sameMiss_at
    G hfree hv p.external_empty p.outer_degree p.mate p.mate_adj
      (⟨u, a⟩ : OneHighAllMatchedVertices G v)).mpr (hsame ⟨u, a⟩)
  have hxMateMiss : oneHighMatchedMissLabel G hfree hv p.external_empty
      p.outer_degree p.mate p.mate_adj s
        (oneHighInternalMate G hfree v s x) = u := by
    change oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
      p.mate p.mate_adj
        (oneHighGlobalInternalMate G hfree v ⟨s, x⟩) = u
    exact hxSame.symm.trans hxMiss
  have haMateMiss : oneHighMatchedMissLabel G hfree hv p.external_empty
      p.outer_degree p.mate p.mate_adj u
        (oneHighInternalMate G hfree v u a) = s := by
    change oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
      p.mate p.mate_adj
        (oneHighGlobalInternalMate G hfree v ⟨u, a⟩) = s
    exact haSame.symm.trans haMiss
  have hxMem := oneHighMatchedMissLabel_mem G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj s x
  have hxmMem := oneHighMatchedMissLabel_mem G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj s
      (oneHighInternalMate G hfree v s x)
  have haMem := oneHighMatchedMissLabel_mem G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj u a
  have hamMem := oneHighMatchedMissLabel_mem G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj u
      (oneHighInternalMate G hfree v u a)
  refine ⟨⟨s, u, by simp [s], hu, x, a, hxMiss, hxMateMiss, haMiss, haMateMiss,
    ?_, ?_, ?_, ?_⟩⟩
  · simpa [hxMiss] using (Finset.mem_filter.mp hxMem).2
  · simpa [hxMateMiss] using (Finset.mem_filter.mp hxmMem).2
  · simpa [haMiss] using (Finset.mem_filter.mp haMem).2
  · simpa [haMateMiss] using (Finset.mem_filter.mp hamMem).2

/-- In every positive profile (in particular the surviving profiles `2` and
`4`), the canonical source branch in the reciprocal witness has exactly one
internal edge. -/
theorem OneHighReciprocalSameMissEdges.source_internalEdges_eq_one
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : 0 < p.profile) :
    oneHighFamilyInternalEdges p.profile (p.branchLabel q.s) = 1 := by
  rw [q.s_label]
  simp [oneHighFamilyInternalEdges, hprofile]

theorem OneHighReciprocalSameMissEdges.source_matched_card_eq_two
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : 0 < p.profile) :
    Fintype.card (OneHighMatchedBranchVertices G v q.s) = 2 := by
  rw [card_oneHighMatchedBranchVertices_eq_highBranchMatchedCount]
  have hcount : highBranchMatchedCount G v q.s =
      2 * oneHighFamilyInternalEdges p.profile (p.branchLabel q.s) := by
    simpa using p.matched_count (p.branchLabel q.s)
  rw [hcount]
  rw [q.source_internalEdges_eq_one hprofile]

theorem OneHighReciprocalSameMissEdges.source_matched_eq_x_or_mate
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : 0 < p.profile)
    (z : OneHighMatchedBranchVertices G v q.s) :
    z = q.x ∨ z = oneHighInternalMate G hfree v q.s q.x := by
  let xm := oneHighInternalMate G hfree v q.s q.x
  have hne : q.x ≠ xm := by
    exact (degreeOneMate_ne _ _ q.x).symm
  have hpairCard : ({q.x, xm} : Finset
      (OneHighMatchedBranchVertices G v q.s)).card = 2 := by
    simp [hne]
  have hunivCard : (Finset.univ : Finset
      (OneHighMatchedBranchVertices G v q.s)).card = 2 := by
    simpa using q.source_matched_card_eq_two hprofile
  have hpairUniv : ({q.x, xm} : Finset
      (OneHighMatchedBranchVertices G v q.s)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (by simp)
    rw [hpairCard, hunivCard]
  have hz : z ∈ ({q.x, xm} : Finset
      (OneHighMatchedBranchVertices G v q.s)) := by
    rw [hpairUniv]
    exact Finset.mem_univ z
  simpa [xm] using hz

/-- In a positive profile, the reciprocal target consumes the entire miss
budget of the canonical source branch: both endpoints of its unique internal
edge miss `u`. -/
theorem OneHighReciprocalSameMissEdges.source_missCount_eq_two
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : 0 < p.profile) :
    highBranchMissCount G v q.s q.u = 2 := by
  have hcard := card_oneHighMatchedMissLabelFiber_eq_highBranchMissCount
    G hfree hv p.external_empty p.outer_degree p.mate p.mate_adj
      q.s q.u q.u_far
  have hfilter : ((Finset.univ : Finset
      (OneHighMatchedBranchVertices G v q.s)).filter fun z =>
        oneHighMatchedMissLabel G hfree hv p.external_empty p.outer_degree
          p.mate p.mate_adj q.s z = q.u) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro z
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ z, ?_⟩
    rcases q.source_matched_eq_x_or_mate hprofile z with rfl | rfl
    · exact q.x_misses_u
    · exact q.x_mate_misses_u
  rw [hfilter] at hcard
  rw [← hcard]
  simpa using q.source_matched_card_eq_two hprofile

/-- No second far branch can receive a miss from the canonical source: the
reciprocal entry `u` already consumes its full row sum. -/
theorem OneHighReciprocalSameMissEdges.source_other_missCount_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : 0 < p.profile)
    {w : {z : V // z ∈ G.neighborSet v}}
    (hw : w ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)))
    (hwu : w ≠ q.u) :
    highBranchMissCount G v q.s w = 0 := by
  let S := ((Finset.univ.erase q.s).erase (p.mate q.s))
  let f := fun z => highBranchMissCount G v q.s z
  have hrow := p.sum_far_missCount G hfree hv q.s
  have hsum : ∑ z ∈ S, f z = 2 := by
    simpa [S, f, q.source_internalEdges_eq_one hprofile] using hrow
  have hu : q.u ∈ S := q.u_far
  have hdecomp := Finset.sum_erase_add S f hu
  have herase : ∑ z ∈ S.erase q.u, f z = 0 := by
    have hmiss : f q.u = 2 := q.source_missCount_eq_two hprofile
    rw [hmiss, hsum] at hdecomp
    omega
  have hwErase : w ∈ S.erase q.u := Finset.mem_erase.mpr ⟨hwu, hw⟩
  have hle : f w ≤ ∑ z ∈ S.erase q.u, f z :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hwErase
  rw [herase] at hle
  exact Nat.eq_zero_of_le_zero hle

/-- Every matched endpoint in the canonical source hits each far branch other
than the unique reciprocal miss branch exactly once.  Thus the reciprocal
witness determines the complete pointwise far-incidence pattern of `s`. -/
theorem OneHighReciprocalSameMissEdges.source_endpoint_hits_other
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : 0 < p.profile)
    (z : OneHighMatchedBranchVertices G v q.s)
    {w : {r : V // r ∈ G.neighborSet v}}
    (hw : w ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)))
    (hwu : w ≠ q.u) :
    (G.neighborFinset z.1.1 ∩ secondLayerBranch G v w).card = 1 := by
  have hzLabel : oneHighMatchedMissLabel G hfree hv p.external_empty
      p.outer_degree p.mate p.mate_adj q.s z = q.u := by
    rcases q.source_matched_eq_x_or_mate hprofile z with rfl | rfl
    · exact q.x_misses_u
    · exact q.x_mate_misses_u
  have hzw : z.1.1 ≠ w.1 := by
    intro h
    have hwBranch : w.1 ∈ secondLayerBranch G v q.s := h.symm ▸ z.1.2
    exact (Finset.mem_sdiff.mp hwBranch).2 (by
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      exact Or.inr w.2)
  have hle := card_neighborFinset_inter_secondLayerBranch_le_one
    G hfree v z.1.1 w hzw
  have hne : (G.neighborFinset z.1.1 ∩
      secondLayerBranch G v w).card ≠ 0 := by
    intro hzero
    have hwMiss : w ∈ oneHighFarMissBranches G v p.mate q.s z.1.1 :=
      Finset.mem_filter.mpr ⟨hw, hzero⟩
    have hzMatched : (G.neighborFinset z.1.1 ∩
        secondLayerBranch G v q.s).card = 1 := by
      rw [← degree_induce_secondLayerBranch_eq_card_inter]
      exact z.2
    have hweq := eq_oneHighMissingBranch_of_matched_of_mem
      G hfree hv p.external_empty p.outer_degree p.mate p.mate_adj
        q.s z.1.1 z.1.2 hzMatched w hwMiss
    apply hwu
    exact hweq.trans hzLabel
  omega

/-- The reciprocal diagonal label pair occurs in the canonical graph pairing
row of the source branch. -/
theorem OneHighReciprocalSameMissEdges.source_diagonalPair_mem_pairing
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p) :
    (p.branchLabel q.u, p.branchLabel q.u) ∈
      oneHighGraphSourcePairing G hfree hv p (p.branchLabel q.s) := by
  let M := oneHighInternalMate G hfree v q.s
  let rootLabel := oneHighMatchedMissLabel G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj q.s
  let label := fun z => p.branchLabel (rootLabel z)
  have hinv : Function.Involutive M := degreeOneMate_involutive _ _
  have hne : M q.x ≠ q.x := degreeOneMate_ne _ _ q.x
  have hmem : (min (label q.x) (label (M q.x)),
      max (label q.x) (label (M q.x))) ∈
      matchingPairingListSorted M label := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm : M q.x ∈ matchingEdgeSources M := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change M q.x < M (M q.x)
        rw [hinv q.x]
        exact hlt
      simpa [hinv q.x, min_comm, max_comm] using
        canonicalPair_mem_matchingPairingListSorted_of_mem_source M label hm
    · exact canonicalPair_mem_matchingPairingListSorted_of_mem_source M label
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩)
  rw [oneHighGraphSourcePairing, p.branchLabel.symm_apply_apply]
  simpa [M, rootLabel, label, q.x_misses_u, q.x_mate_misses_u] using hmem

/-- In a positive profile, the canonical pairing row is literally the
singleton reciprocal diagonal pair. -/
theorem OneHighReciprocalSameMissEdges.source_pairing_eq_singleton
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : 0 < p.profile) :
    oneHighGraphSourcePairing G hfree hv p (p.branchLabel q.s) =
      [(p.branchLabel q.u, p.branchLabel q.u)] := by
  have hlen := oneHighGraphSourcePairing_length G hfree hv p
    (p.branchLabel q.s)
  rw [q.source_internalEdges_eq_one hprofile] at hlen
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp hlen
  have hmem := q.source_diagonalPair_mem_pairing
  rw [ha] at hmem ⊢
  exact congrArg List.singleton (List.mem_singleton.mp hmem).symm

/-- Certificate-facing form of the reconstructed reciprocal row: the source
zero compatible-pairing search space contains its exact diagonal singleton. -/
theorem OneHighReciprocalSameMissEdges.source_singleton_mem_compatible
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : 0 < p.profile) :
    [(p.branchLabel q.u, p.branchLabel q.u)] ∈
      oneHighCompatibleSourcePairings p.profile
        (oneHighGraphRelevantMissTable
          (oneHighRelabeledLeafGraph G v
            (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
          p.profile)
        0 := by
  have hmem := oneHighGraphSourcePairing_mem_compatible G hfree hv p
    (p.branchLabel q.s)
  rw [q.source_pairing_eq_singleton hprofile, q.s_label] at hmem
  exact hmem

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
