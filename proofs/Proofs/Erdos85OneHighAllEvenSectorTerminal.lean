import Proofs.Erdos85OneHighStructuralTerminalInterface
import Proofs.Erdos85OneHighExchangedMissCounting
import Proofs.Erdos85OneHighSameMissCountingBridge
import Proofs.Erdos85OneHighSameMissParityConsumer
import Proofs.Erdos85QuotientCutParity
import Proofs.Erdos85OneHighRepeatedSourceCapacity
import Proofs.Erdos85OneHighGraphPairingRefinement
import Proofs.Erdos85OneHighReciprocalTwoCycleInventory

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

/-- Complete graph-facing residual for the all-even sector: either global
same-miss behavior yields reciprocal concrete edges, or the repeated
exchanged-key branch yields two concrete source edges with the exact
owner/capacity trichotomy. -/
theorem oneHigh_reciprocal_or_repeatedResidual_of_all_even
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
    Nonempty (OneHighReciprocalSameMissEdges G hfree hv p) ∨
      Nonempty (OneHighOddProfileRepeatedPairResidual G hfree hv p) := by
  rcases oneHigh_globalSameMiss_or_repeated_exchangedPair_of_all_even
      G hfree hv p heven with hsame | hrepeated
  · exact Or.inl (exists_oneHighReciprocalSameMissEdges G hfree hv p hsame)
  · right
    obtain ⟨key, hkey, x, hx, y, hy, hxy, hxkey, hykey⟩ := hrepeated
    refine ⟨⟨key, hkey, x, y, hx, hy, hxy, hxkey, hykey, ?_⟩⟩
    by_cases howner : x.1 = y.1
    · exact Or.inl ⟨howner,
        oneHighFamilyInternalEdges_eq_two_of_distinct_sources_sameOwner
          G hfree hv p hx hy hxy howner⟩
    by_cases hmateOwner : x.1 = p.mate y.1
    · exact Or.inr (Or.inl hmateOwner)
    · exact Or.inr (Or.inr ⟨howner, hmateOwner⟩)

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

/-- Vertex-level form of `source_endpoint_hits_other`: each canonical-source
endpoint has a unique neighbor in every non-missed far branch. -/
theorem OneHighReciprocalSameMissEdges.existsUnique_source_neighbor_other
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
    ∃! y : V, y ∈ secondLayerBranch G v w ∧ G.Adj z.1.1 y := by
  have hcard := q.source_endpoint_hits_other hprofile z hw hwu
  obtain ⟨y, hy⟩ := Finset.card_eq_one.mp hcard
  refine ⟨y, ?_, ?_⟩
  · have hymem : y ∈ G.neighborFinset z.1.1 ∩
        secondLayerBranch G v w := by
      rw [hy]
      exact Finset.mem_singleton_self y
    exact ⟨(Finset.mem_inter.mp hymem).2,
      (G.mem_neighborFinset z.1.1 y).mp (Finset.mem_inter.mp hymem).1⟩
  · intro y' hy'
    have hy'mem : y' ∈ G.neighborFinset z.1.1 ∩
        secondLayerBranch G v w := Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z.1.1 y').mpr hy'.2, hy'.1⟩
    rw [hy] at hy'mem
    exact Finset.mem_singleton.mp hy'mem

/-- Any endpoint of the canonical source edge and any endpoint of the reverse
edge have at most one common neighbor.  Consequently their unique witnesses
in distinct third branches cannot collide twice. -/
theorem OneHighReciprocalSameMissEdges.source_reverse_common_le_one
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (z : OneHighMatchedBranchVertices G v q.s)
    (b : OneHighMatchedBranchVertices G v q.u) :
    (G.neighborFinset z.1.1 ∩ G.neighborFinset b.1.1).card ≤ 1 := by
  have hus : q.u ≠ q.s :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp q.u_far).2).1
  have hdisj : Disjoint (secondLayerBranch G v q.s)
      (secondLayerBranch G v q.u) :=
    secondLayerBranch_pairwiseDisjoint G hfree v
      (by simp) (by simp) hus.symm
  have hne : z.1.1 ≠ b.1.1 := by
    intro h
    have hbSource : b.1.1 ∈ secondLayerBranch G v q.s := h.symm ▸ z.1.2
    exact Finset.disjoint_left.mp hdisj hbSource b.1.2
  exact common_le_one_of_not_containsC4 hfree z.1.1 b.1.1 hne

theorem OneHighReciprocalSameMissEdges.source_reverse_commonNeighbor_unique
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (z : OneHighMatchedBranchVertices G v q.s)
    (b : OneHighMatchedBranchVertices G v q.u)
    {y y' : V}
    (hzy : G.Adj z.1.1 y) (hby : G.Adj b.1.1 y)
    (hzy' : G.Adj z.1.1 y') (hby' : G.Adj b.1.1 y') :
    y = y' := by
  apply Finset.card_le_one.mp (q.source_reverse_common_le_one z b)
  · exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z.1.1 y).mpr hzy,
        (G.mem_neighborFinset b.1.1 y).mpr hby⟩
  · exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset z.1.1 y').mpr hzy',
        (G.mem_neighborFinset b.1.1 y').mpr hby'⟩

/-- A fixed source/reverse endpoint pair can collide in at most one root
branch: two branches containing common neighbors of the same endpoints must
be equal. -/
theorem OneHighReciprocalSameMissEdges.source_reverse_commonBranch_unique
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (z : OneHighMatchedBranchVertices G v q.s)
    (b : OneHighMatchedBranchVertices G v q.u)
    {w w' : {r : V // r ∈ G.neighborSet v}}
    (hw : ∃ y : V, y ∈ secondLayerBranch G v w ∧
      G.Adj z.1.1 y ∧ G.Adj b.1.1 y)
    (hw' : ∃ y : V, y ∈ secondLayerBranch G v w' ∧
      G.Adj z.1.1 y ∧ G.Adj b.1.1 y) :
    w = w' := by
  by_contra hww'
  obtain ⟨y, hyBranch, hzy, hby⟩ := hw
  obtain ⟨y', hy'Branch, hzy', hby'⟩ := hw'
  have hyy' := q.source_reverse_commonNeighbor_unique z b
    hzy hby hzy' hby'
  subst y'
  have hdisj : Disjoint (secondLayerBranch G v w)
      (secondLayerBranch G v w') :=
    secondLayerBranch_pairwiseDisjoint G hfree v
      (by simp) (by simp) hww'
  exact Finset.disjoint_left.mp hdisj hyBranch hy'Branch

/-- Root branches containing a common neighbor of a fixed source/reverse
endpoint pair. -/
def OneHighReciprocalSameMissEdges.collisionBranches
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (z : OneHighMatchedBranchVertices G v q.s)
    (b : OneHighMatchedBranchVertices G v q.u) :
    Finset {r : V // r ∈ G.neighborSet v} :=
  Finset.univ.filter fun w =>
    (G.neighborFinset z.1.1 ∩ G.neighborFinset b.1.1 ∩
      secondLayerBranch G v w).Nonempty

theorem OneHighReciprocalSameMissEdges.collisionBranches_card_le_one
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (z : OneHighMatchedBranchVertices G v q.s)
    (b : OneHighMatchedBranchVertices G v q.u) :
    (q.collisionBranches z b).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro w hw w' hw'
  have hwNonempty := (Finset.mem_filter.mp hw).2
  have hw'Nonempty := (Finset.mem_filter.mp hw').2
  obtain ⟨y, hy⟩ := hwNonempty
  obtain ⟨y', hy'⟩ := hw'Nonempty
  have hyp := Finset.mem_inter.mp hy
  have hyp' := Finset.mem_inter.mp hy'
  exact q.source_reverse_commonBranch_unique z b
    ⟨y, hyp.2, (G.mem_neighborFinset z.1.1 y).mp
      (Finset.mem_inter.mp hyp.1).1,
      (G.mem_neighborFinset b.1.1 y).mp (Finset.mem_inter.mp hyp.1).2⟩
    ⟨y', hyp'.2, (G.mem_neighborFinset z.1.1 y').mp
      (Finset.mem_inter.mp hyp'.1).1,
      (G.mem_neighborFinset b.1.1 y').mp (Finset.mem_inter.mp hyp'.1).2⟩

/-- Across the two endpoints of each reciprocal internal edge, at most four
root branches can contain any source/reverse endpoint collision. -/
theorem OneHighReciprocalSameMissEdges.all_collisionBranches_card_le_four
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p) :
    let xm := oneHighInternalMate G hfree v q.s q.x
    let am := oneHighInternalMate G hfree v q.u q.a
    ((((q.collisionBranches q.x q.a) ∪ q.collisionBranches q.x am) ∪
      q.collisionBranches xm q.a) ∪ q.collisionBranches xm am).card ≤ 4 := by
  dsimp only
  have hxa := q.collisionBranches_card_le_one q.x q.a
  have hxam := q.collisionBranches_card_le_one q.x
    (oneHighInternalMate G hfree v q.u q.a)
  have hma := q.collisionBranches_card_le_one
    (oneHighInternalMate G hfree v q.s q.x) q.a
  have hmam := q.collisionBranches_card_le_one
    (oneHighInternalMate G hfree v q.s q.x)
    (oneHighInternalMate G hfree v q.u q.a)
  have h₁ := Finset.card_union_le
    (q.collisionBranches q.x q.a)
    (q.collisionBranches q.x (oneHighInternalMate G hfree v q.u q.a))
  have h₂ := Finset.card_union_le
    ((q.collisionBranches q.x q.a) ∪
      q.collisionBranches q.x (oneHighInternalMate G hfree v q.u q.a))
    (q.collisionBranches (oneHighInternalMate G hfree v q.s q.x) q.a)
  have h₃ := Finset.card_union_le
    (((q.collisionBranches q.x q.a) ∪
      q.collisionBranches q.x (oneHighInternalMate G hfree v q.u q.a)) ∪
      q.collisionBranches (oneHighInternalMate G hfree v q.s q.x) q.a)
    (q.collisionBranches (oneHighInternalMate G hfree v q.s q.x)
      (oneHighInternalMate G hfree v q.u q.a))
  omega

/-- In every non-missed far branch, the two neighbors reached from the
canonical source edge form a forced nonedge. -/
theorem OneHighReciprocalSameMissEdges.exists_source_crossTargets_nonadjacent
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : 0 < p.profile)
    {w : {r : V // r ∈ G.neighborSet v}}
    (hw : w ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)))
    (hwu : w ≠ q.u) :
    ∃ y y' : V,
      y ∈ secondLayerBranch G v w ∧
      y' ∈ secondLayerBranch G v w ∧
      G.Adj q.x.1.1 y ∧
      G.Adj (oneHighInternalMate G hfree v q.s q.x).1.1 y' ∧
      y ≠ y' ∧
      ¬ G.Adj y y' := by
  have hsw : q.s ≠ w := by
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hw).2).1.symm
  have hxy : G.Adj q.x.1.1
      (oneHighInternalMate G hfree v q.s q.x).1.1 := by
    simpa [oneHighInternalMate] using degreeOneMate_adj
      (G.induce (secondLayerBranch G v q.s))
      (degree_induce_secondLayerBranch_le_one G hfree v q.s) q.x
  have hxHit : (G.neighborFinset q.x.1.1 ∩
      secondLayerBranch G v w).card ≠ 0 := by
    rw [q.source_endpoint_hits_other hprofile q.x hw hwu]
    omega
  have hmHit : (G.neighborFinset
      (oneHighInternalMate G hfree v q.s q.x).1.1 ∩
      secondLayerBranch G v w).card ≠ 0 := by
    rw [q.source_endpoint_hits_other hprofile
      (oneHighInternalMate G hfree v q.s q.x) hw hwu]
    omega
  obtain ⟨y, y', hy, hy', hxyTarget, hmTarget, hnonadj⟩ :=
    exists_nonadjacent_crossTargets_of_internalEdge
    G hfree q.s w hsw q.x.1.2
      (oneHighInternalMate G hfree v q.s q.x).1.2 hxy hxHit hmHit
  refine ⟨y, y', hy, hy', hxyTarget, hmTarget, ?_, hnonadj⟩
  intro hyy'
  subst y'
  have hendNe : q.x.1.1 ≠
      (oneHighInternalMate G hfree v q.s q.x).1.1 := by
    intro hval
    apply degreeOneMate_ne (G.induce (secondLayerBranch G v q.s))
      (degree_induce_secondLayerBranch_le_one G hfree v q.s) q.x
    exact Subtype.ext (Subtype.ext hval.symm)
  have hcommon := common_le_one_of_not_containsC4 hfree q.x.1.1
    (oneHighInternalMate G hfree v q.s q.x).1.1 hendNe
  have hyCommon : y ∈ G.neighborFinset q.x.1.1 ∩
      G.neighborFinset (oneHighInternalMate G hfree v q.s q.x).1.1 :=
    Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset q.x.1.1 y).mpr hxyTarget,
        (G.mem_neighborFinset
          (oneHighInternalMate G hfree v q.s q.x).1.1 y).mpr hmTarget⟩
  have hsCommon : q.s.1 ∈ G.neighborFinset q.x.1.1 ∩
      G.neighborFinset (oneHighInternalMate G hfree v q.s q.x).1.1 := by
    apply Finset.mem_inter.mpr
    constructor
    · exact (G.mem_neighborFinset q.x.1.1 q.s.1).mpr
        ((G.mem_neighborFinset q.s.1 q.x.1.1).mp
          (Finset.mem_sdiff.mp q.x.1.2).1).symm
    · exact (G.mem_neighborFinset
        (oneHighInternalMate G hfree v q.s q.x).1.1 q.s.1).mpr
        ((G.mem_neighborFinset q.s.1
          (oneHighInternalMate G hfree v q.s q.x).1.1).mp
            (Finset.mem_sdiff.mp
              (oneHighInternalMate G hfree v q.s q.x).1.2).1).symm
  have hyEqS := Finset.card_le_one.mp hcommon y hyCommon q.s.1 hsCommon
  have hyNeS : y ≠ q.s.1 := by
    intro h
    subst y
    exact (Finset.mem_sdiff.mp hy).2 (by
      simp only [Finset.mem_insert, SimpleGraph.mem_neighborFinset]
      exact Or.inr q.s.2)
  exact hyNeS hyEqS

/-- A branch with exactly one internal edge has only two matched vertices, so
any two distinct matched vertices are the endpoints of that edge. -/
theorem adj_of_distinct_oneHighMatchedBranchVertices_of_internalEdges_eq_one
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V}
    {p : OneHighRawV2Presentation G hfree v}
    {s : {r : V // r ∈ G.neighborSet v}}
    (hedge : oneHighFamilyInternalEdges p.profile (p.branchLabel s) = 1)
    (y y' : OneHighMatchedBranchVertices G v s) (hyy' : y ≠ y') :
    G.Adj y.1.1 y'.1.1 := by
  have hcard : Fintype.card (OneHighMatchedBranchVertices G v s) = 2 := by
    rw [card_oneHighMatchedBranchVertices_eq_highBranchMatchedCount]
    have hcount := p.matched_count (p.branchLabel s)
    simpa [hedge] using hcount
  let ym := oneHighInternalMate G hfree v s y
  have hymNe : ym ≠ y := degreeOneMate_ne _ _ y
  have hpairCard : ({y, ym} : Finset
      (OneHighMatchedBranchVertices G v s)).card = 2 := by
    simp [hymNe.symm]
  have hunivCard : (Finset.univ : Finset
      (OneHighMatchedBranchVertices G v s)).card = 2 := by
    simpa using hcard
  have hpairUniv : ({y, ym} : Finset
      (OneHighMatchedBranchVertices G v s)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (by simp)
    rw [hpairCard, hunivCard]
  have hy'mem : y' ∈ ({y, ym} : Finset
      (OneHighMatchedBranchVertices G v s)) := by
    rw [hpairUniv]
    exact Finset.mem_univ y'
  have hy'eq : y' = ym := by
    rcases Finset.mem_insert.mp hy'mem with hy'y | hy'ym
    · exact False.elim (hyy' hy'y.symm)
    · exact Finset.mem_singleton.mp hy'ym
  rw [hy'eq]
  change G.Adj y.1.1
    (degreeOneMate (G.induce (secondLayerBranch G v s))
      (degree_induce_secondLayerBranch_le_one G hfree v s) y).1.1
  simpa using degreeOneMate_adj
    (G.induce (secondLayerBranch G v s))
    (degree_induce_secondLayerBranch_le_one G hfree v s) y

/-- The chosen edge exhausts the matched vertices of a one-edge branch. -/
theorem oneHighMatchedBranchVertex_eq_or_internalMate_of_internalEdges_eq_one
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V}
    {p : OneHighRawV2Presentation G hfree v}
    {s : {r : V // r ∈ G.neighborSet v}}
    (hedge : oneHighFamilyInternalEdges p.profile (p.branchLabel s) = 1)
    (a z : OneHighMatchedBranchVertices G v s) :
    z = a ∨ z = oneHighInternalMate G hfree v s a := by
  let am := oneHighInternalMate G hfree v s a
  have hamNe : am ≠ a := degreeOneMate_ne _ _ a
  have hcard : Fintype.card (OneHighMatchedBranchVertices G v s) = 2 := by
    rw [card_oneHighMatchedBranchVertices_eq_highBranchMatchedCount]
    have hcount := p.matched_count (p.branchLabel s)
    simpa [hedge] using hcount
  have hpairCard : ({a, am} : Finset
      (OneHighMatchedBranchVertices G v s)).card = 2 := by
    simp [hamNe.symm]
  have hunivCard : (Finset.univ : Finset
      (OneHighMatchedBranchVertices G v s)).card = 2 := by
    simpa using hcard
  have hpairUniv : ({a, am} : Finset
      (OneHighMatchedBranchVertices G v s)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (by simp)
    rw [hpairCard, hunivCard]
  have hzMem : z ∈ ({a, am} : Finset
      (OneHighMatchedBranchVertices G v s)) := by
    rw [hpairUniv]
    exact Finset.mem_univ z
  simpa [am] using hzMem

/-- If the reciprocal target branch has one internal edge, its selected
reverse edge exhausts that branch and both endpoints miss the source. -/
theorem OneHighReciprocalSameMissEdges.reverse_missCount_eq_two_of_internalEdges_eq_one
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (huEdge : oneHighFamilyInternalEdges p.profile (p.branchLabel q.u) = 1) :
    highBranchMissCount G v q.u q.s = 2 := by
  have husFar : q.s ∈ ((Finset.univ.erase q.u).erase (p.mate q.u)) := by
    have hum : q.u ≠ p.mate q.s := (Finset.mem_erase.mp q.u_far).1
    have hus : q.u ≠ q.s :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp q.u_far).2).1
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_erase.mpr ⟨hus.symm, Finset.mem_univ _⟩⟩
    intro hsm
    apply hum
    exact (p.mate_involutive q.u).symm.trans (congrArg p.mate hsm).symm
  have hfilter : ((Finset.univ : Finset
      (OneHighMatchedBranchVertices G v q.u)).filter fun z =>
        oneHighMatchedMissLabel G hfree hv p.external_empty p.outer_degree
          p.mate p.mate_adj q.u z = q.s) = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro z
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ z, ?_⟩
    rcases oneHighMatchedBranchVertex_eq_or_internalMate_of_internalEdges_eq_one
      huEdge q.a z with rfl | rfl
    · exact q.a_misses_s
    · exact q.a_mate_misses_s
  have hfiber := card_oneHighMatchedMissLabelFiber_eq_highBranchMissCount
    G hfree hv p.external_empty p.outer_degree p.mate p.mate_adj
      q.u q.s husFar
  rw [hfilter] at hfiber
  rw [← hfiber]
  change Fintype.card (OneHighMatchedBranchVertices G v q.u) = 2
  rw [card_oneHighMatchedBranchVertices_eq_highBranchMatchedCount]
  have hcount := p.matched_count (p.branchLabel q.u)
  simpa [huEdge] using hcount

/-- In the one-edge reciprocal-target case, the reverse miss row is supported
only at the canonical source branch. -/
theorem OneHighReciprocalSameMissEdges.reverse_other_missCount_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (huEdge : oneHighFamilyInternalEdges p.profile (p.branchLabel q.u) = 1)
    {w : {r : V // r ∈ G.neighborSet v}}
    (hw : w ∈ ((Finset.univ.erase q.u).erase (p.mate q.u)))
    (hws : w ≠ q.s) :
    highBranchMissCount G v q.u w = 0 := by
  let S := ((Finset.univ.erase q.u).erase (p.mate q.u))
  let f := fun z => highBranchMissCount G v q.u z
  have hrow := p.sum_far_missCount G hfree hv q.u
  have hsum : ∑ z ∈ S, f z = 2 := by
    simpa [S, f, huEdge] using hrow
  have hsFar : q.s ∈ S := by
    have hum : q.u ≠ p.mate q.s := (Finset.mem_erase.mp q.u_far).1
    have hus : q.u ≠ q.s :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp q.u_far).2).1
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_erase.mpr ⟨hus.symm, Finset.mem_univ _⟩⟩
    intro hsm
    apply hum
    exact (p.mate_involutive q.u).symm.trans (congrArg p.mate hsm).symm
  have hdecomp := Finset.sum_erase_add S f hsFar
  have herase : ∑ z ∈ S.erase q.s, f z = 0 := by
    have hmiss : f q.s = 2 :=
      q.reverse_missCount_eq_two_of_internalEdges_eq_one huEdge
    rw [hmiss, hsum] at hdecomp
    omega
  have hwErase : w ∈ S.erase q.s := Finset.mem_erase.mpr ⟨hws, hw⟩
  have hle : f w ≤ ∑ z ∈ S.erase q.s, f z :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) hwErase
  rw [herase] at hle
  exact Nat.eq_zero_of_le_zero hle

theorem OneHighReciprocalSameMissEdges.reverse_diagonalPair_mem_pairing
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p) :
    (p.branchLabel q.s, p.branchLabel q.s) ∈
      oneHighGraphSourcePairing G hfree hv p (p.branchLabel q.u) := by
  let M := oneHighInternalMate G hfree v q.u
  let rootLabel := oneHighMatchedMissLabel G hfree hv p.external_empty
    p.outer_degree p.mate p.mate_adj q.u
  let label := fun z => p.branchLabel (rootLabel z)
  have hinv : Function.Involutive M := degreeOneMate_involutive _ _
  have hne : M q.a ≠ q.a := degreeOneMate_ne _ _ q.a
  have hmem : (min (label q.a) (label (M q.a)),
      max (label q.a) (label (M q.a))) ∈
      matchingPairingListSorted M label := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm : M q.a ∈ matchingEdgeSources M := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change M q.a < M (M q.a)
        rw [hinv q.a]
        exact hlt
      simpa [hinv q.a, min_comm, max_comm] using
        canonicalPair_mem_matchingPairingListSorted_of_mem_source M label hm
    · exact canonicalPair_mem_matchingPairingListSorted_of_mem_source M label
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩)
  rw [oneHighGraphSourcePairing, p.branchLabel.symm_apply_apply]
  simpa [M, rootLabel, label, q.a_misses_s, q.a_mate_misses_s] using hmem

/-- When both reciprocal branches have one edge, the reverse canonical
pairing row is the diagonal singleton back to source label `0`. -/
theorem OneHighReciprocalSameMissEdges.reverse_pairing_eq_singleton
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (huEdge : oneHighFamilyInternalEdges p.profile (p.branchLabel q.u) = 1) :
    oneHighGraphSourcePairing G hfree hv p (p.branchLabel q.u) =
      [(p.branchLabel q.s, p.branchLabel q.s)] := by
  have hlen := oneHighGraphSourcePairing_length G hfree hv p
    (p.branchLabel q.u)
  rw [huEdge] at hlen
  obtain ⟨pair, hpair⟩ := List.length_eq_one_iff.mp hlen
  have hmem := q.reverse_diagonalPair_mem_pairing
  rw [hpair] at hmem ⊢
  exact congrArg List.singleton (List.mem_singleton.mp hmem).symm

/-- In a one-edge target branch, the forced distinct nonadjacent targets of
the canonical source edge cannot both be internally matched. -/
theorem OneHighReciprocalSameMissEdges.exists_source_crossTargets_with_isolated
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : 0 < p.profile)
    {w : {r : V // r ∈ G.neighborSet v}}
    (hw : w ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)))
    (hwu : w ≠ q.u)
    (hwEdge : oneHighFamilyInternalEdges p.profile (p.branchLabel w) = 1) :
    ∃ y y' : V,
      y ∈ secondLayerBranch G v w ∧
      y' ∈ secondLayerBranch G v w ∧
      G.Adj q.x.1.1 y ∧
      G.Adj (oneHighInternalMate G hfree v q.s q.x).1.1 y' ∧
      y ≠ y' ∧ ¬ G.Adj y y' ∧
      ((G.neighborFinset y ∩ secondLayerBranch G v w).card = 0 ∨
       (G.neighborFinset y' ∩ secondLayerBranch G v w).card = 0) := by
  obtain ⟨y, y', hy, hy', hxy, hmy', hne, hnonadj⟩ :=
    q.exists_source_crossTargets_nonadjacent hprofile hw hwu
  refine ⟨y, y', hy, hy', hxy, hmy', hne, hnonadj, ?_⟩
  by_contra hboth
  push Not at hboth
  have hyLe := degree_induce_secondLayerBranch_le_one G hfree v w ⟨y, hy⟩
  have hy'Le := degree_induce_secondLayerBranch_le_one G hfree v w ⟨y', hy'⟩
  rw [degree_induce_secondLayerBranch_eq_card_inter] at hyLe hy'Le
  have hyLe' : (G.neighborFinset y ∩
      secondLayerBranch G v w).card ≤ 1 := by simpa using hyLe
  have hy'Le' : (G.neighborFinset y' ∩
      secondLayerBranch G v w).card ≤ 1 := by simpa using hy'Le
  have hyCard : (G.neighborFinset y ∩ secondLayerBranch G v w).card = 1 := by
    omega
  have hy'Card : (G.neighborFinset y' ∩ secondLayerBranch G v w).card = 1 := by
    omega
  have hyOne : (G.induce (secondLayerBranch G v w)).degree ⟨y, hy⟩ = 1 := by
    rw [degree_induce_secondLayerBranch_eq_card_inter]
    exact hyCard
  have hy'One : (G.induce (secondLayerBranch G v w)).degree ⟨y', hy'⟩ = 1 := by
    rw [degree_induce_secondLayerBranch_eq_card_inter]
    exact hy'Card
  let Y : OneHighMatchedBranchVertices G v w := ⟨⟨y, hy⟩, hyOne⟩
  let Y' : OneHighMatchedBranchVertices G v w := ⟨⟨y', hy'⟩, hy'One⟩
  have hYY' : Y ≠ Y' := by
    intro h
    apply hne
    exact congrArg (fun z : OneHighMatchedBranchVertices G v w => z.1.1) h
  exact hnonadj
    (adj_of_distinct_oneHighMatchedBranchVertices_of_internalEdges_eq_one
      hwEdge Y Y' hYY')

/-- Finite profile-4 arithmetic: after removing source label `0`, its mate
`1`, and any reciprocal target, at least two distinct one-edge branch labels
remain. -/
theorem exists_two_other_oneEdge_labels_profile_four
    (u : Fin 8) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    ∃ w₁ w₂ : Fin 8,
      w₁ ≠ w₂ ∧ w₁ ≠ 0 ∧ w₁ ≠ 1 ∧ w₁ ≠ u ∧
      w₂ ≠ 0 ∧ w₂ ≠ 1 ∧ w₂ ≠ u ∧
      oneHighFamilyInternalEdges 4 w₁ = 1 ∧
      oneHighFamilyInternalEdges 4 w₂ = 1 := by
  native_decide +revert

/-- Packaged isolated-target witness in a far branch. -/
structure OneHighReciprocalIsolatedTarget
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (w : {r : V // r ∈ G.neighborSet v}) where
  y : V
  y' : V
  y_mem : y ∈ secondLayerBranch G v w
  y'_mem : y' ∈ secondLayerBranch G v w
  x_adj_y : G.Adj q.x.1.1 y
  xmate_adj_y' : G.Adj
    (oneHighInternalMate G hfree v q.s q.x).1.1 y'
  ne : y ≠ y'
  nonadj : ¬ G.Adj y y'
  isolated :
    (G.neighborFinset y ∩ secondLayerBranch G v w).card = 0 ∨
    (G.neighborFinset y' ∩ secondLayerBranch G v w).card = 0

theorem OneHighReciprocalSameMissEdges.nonempty_isolatedTarget
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : 0 < p.profile)
    {w : {r : V // r ∈ G.neighborSet v}}
    (hw : w ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)))
    (hwu : w ≠ q.u)
    (hwEdge : oneHighFamilyInternalEdges p.profile (p.branchLabel w) = 1) :
    Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w) := by
  obtain ⟨y, y', hy, hy', hxy, hmy', hne, hnonadj, hisolated⟩ :=
    q.exists_source_crossTargets_with_isolated hprofile hw hwu hwEdge
  exact ⟨⟨y, y', hy, hy', hxy, hmy', hne, hnonadj, hisolated⟩⟩

/-- Profile `4` forces isolated reciprocal source targets in two distinct
one-edge branches. -/
theorem OneHighReciprocalSameMissEdges.exists_two_profileFour_isolatedTargets
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : p.profile = 4) :
    ∃ w₁ w₂ : {r : V // r ∈ G.neighborSet v},
      w₁ ≠ w₂ ∧
      Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₁) ∧
      Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w₂) := by
  have hus : q.u ≠ q.s :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp q.u_far).2).1
  have hum : q.u ≠ p.mate q.s := (Finset.mem_erase.mp q.u_far).1
  have hu0 : p.branchLabel q.u ≠ 0 := by
    intro hu
    apply hus
    apply p.branchLabel.injective
    rw [hu, q.s_label]
  have hu1 : p.branchLabel q.u ≠ 1 := by
    intro hu
    apply hum
    apply p.branchLabel.injective
    rw [hu, p.branch_mate, q.s_label]
    native_decide
  obtain ⟨i₁, i₂, hiNe, hi10, hi11, hi1u, hi20, hi21, hi2u,
      hi1Edge, hi2Edge⟩ :=
    exists_two_other_oneEdge_labels_profile_four (p.branchLabel q.u) hu0 hu1
  let w₁ := p.branchLabel.symm i₁
  let w₂ := p.branchLabel.symm i₂
  have farMem (i : Fin 8) (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
      p.branchLabel.symm i ∈
        ((Finset.univ.erase q.s).erase (p.mate q.s)) := by
    apply Finset.mem_erase.mpr
    constructor
    · intro heq
      apply hi1
      have hlabel := congrArg p.branchLabel heq
      have hmate01 : oneHighStandardMate (0 : Fin 8) = 1 := by native_decide
      simpa [p.branch_mate, q.s_label, hmate01] using hlabel
    · apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      intro heq
      apply hi0
      have hlabel := congrArg p.branchLabel heq
      simpa [q.s_label] using hlabel
  have hw₁ : w₁ ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)) :=
    farMem i₁ hi10 hi11
  have hw₂ : w₂ ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)) :=
    farMem i₂ hi20 hi21
  have hw₁u : w₁ ≠ q.u := by
    intro heq
    apply hi1u
    simpa [w₁] using congrArg p.branchLabel heq
  have hw₂u : w₂ ≠ q.u := by
    intro heq
    apply hi2u
    simpa [w₂] using congrArg p.branchLabel heq
  have hw₁Edge : oneHighFamilyInternalEdges p.profile
      (p.branchLabel w₁) = 1 := by
    simpa [hprofile, w₁] using hi1Edge
  have hw₂Edge : oneHighFamilyInternalEdges p.profile
      (p.branchLabel w₂) = 1 := by
    simpa [hprofile, w₂] using hi2Edge
  have hpos : 0 < p.profile := by omega
  refine ⟨w₁, w₂, ?_,
    q.nonempty_isolatedTarget hpos hw₁ hw₁u hw₁Edge,
    q.nonempty_isolatedTarget hpos hw₂ hw₂u hw₂Edge⟩
  intro heq
  apply hiNe
  simpa [w₁, w₂] using congrArg p.branchLabel heq

/-- Profile `2` dichotomy: either the reciprocal target is label `2`, hence
it is itself a one-edge branch, or label `2` is a distinct available
one-edge target. -/
theorem profile_two_reciprocalTarget_or_other_oneEdge
    (u : Fin 8) (hu0 : u ≠ 0) (hu1 : u ≠ 1) :
    u = 2 ∨
      ((2 : Fin 8) ≠ u ∧ oneHighFamilyInternalEdges 2 (2 : Fin 8) = 1) := by
  native_decide +revert

/-- Graph-facing profile-2 residual: the reciprocal branch has one internal
edge, or a distinct one-edge branch contains a forced isolated source target. -/
theorem OneHighReciprocalSameMissEdges.profileTwo_targetOneEdge_or_isolatedTarget
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : p.profile = 2) :
    oneHighFamilyInternalEdges p.profile (p.branchLabel q.u) = 1 ∨
      ∃ w : {r : V // r ∈ G.neighborSet v},
        w ≠ q.u ∧
        Nonempty (OneHighReciprocalIsolatedTarget G hfree hv p q w) := by
  have hus : q.u ≠ q.s :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp q.u_far).2).1
  have hum : q.u ≠ p.mate q.s := (Finset.mem_erase.mp q.u_far).1
  have hu0 : p.branchLabel q.u ≠ 0 := by
    intro hu
    apply hus
    apply p.branchLabel.injective
    rw [hu, q.s_label]
  have hu1 : p.branchLabel q.u ≠ 1 := by
    intro hu
    apply hum
    apply p.branchLabel.injective
    rw [hu, p.branch_mate, q.s_label]
    native_decide
  rcases profile_two_reciprocalTarget_or_other_oneEdge
      (p.branchLabel q.u) hu0 hu1 with hu2 | ⟨h2u, h2Edge⟩
  · left
    rw [hprofile, hu2]
    native_decide
  · right
    let w := p.branchLabel.symm (2 : Fin 8)
    have hw : w ∈ ((Finset.univ.erase q.s).erase (p.mate q.s)) := by
      apply Finset.mem_erase.mpr
      constructor
      · intro heq
        have hlabel := congrArg p.branchLabel heq
        have hmate01 : oneHighStandardMate (0 : Fin 8) = 1 := by native_decide
        have : (2 : Fin 8) = 1 := by
          simpa [w, p.branch_mate, q.s_label, hmate01] using hlabel
        have hval := congrArg Fin.val this
        norm_num at hval
      · apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_univ _⟩
        intro heq
        have hlabel := congrArg p.branchLabel heq
        have : (2 : Fin 8) = 0 := by simpa [w, q.s_label] using hlabel
        have hval := congrArg Fin.val this
        norm_num at hval
    have hwu : w ≠ q.u := by
      intro heq
      apply h2u
      simpa [w] using congrArg p.branchLabel heq
    have hwEdge : oneHighFamilyInternalEdges p.profile
        (p.branchLabel w) = 1 := by
      simpa [hprofile, w] using h2Edge
    exact ⟨w, hwu, q.nonempty_isolatedTarget (by omega) hw hwu hwEdge⟩

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

/-- Executable inventory signature forced by the graph-side reciprocal
same-miss witness. -/
theorem OneHighReciprocalSameMissEdges.graphTable_has_sourceZeroDiagonalSingleton
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : 0 < p.profile) :
    oneHighTableHasSourceZeroDiagonalSingleton p.profile
      (oneHighGraphRelevantMissTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) = true :=
  oneHighTableHasSourceZeroDiagonalSingleton_of_mem
    (q.source_singleton_mem_compatible hprofile)

/-- In the one-edge reciprocal-target arm, the graph table carries the full
two-sided diagonal cycle: source zero pairs only toward `u`, and source `u`
pairs only back toward zero.  This is the sound graph-facing socket for the
78-row profile-2 finite inventory. -/
theorem OneHighReciprocalSameMissEdges.graphTable_has_reciprocalDiagonalTwoCycle
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {hfree : ¬ containsC4 V G} {v : V} {hv : G.degree v = 8}
    {p : OneHighRawV2Presentation G hfree v}
    (q : OneHighReciprocalSameMissEdges G hfree hv p)
    (hprofile : 0 < p.profile)
    (huEdge : oneHighFamilyInternalEdges p.profile (p.branchLabel q.u) = 1) :
    oneHighTableHasReciprocalDiagonalTwoCycle p.profile
      (oneHighGraphRelevantMissTable
        (oneHighRelabeledLeafGraph G v
          (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
        p.profile) = true := by
  apply oneHighTableHasReciprocalDiagonalTwoCycle_of_mem huEdge
      (q.source_singleton_mem_compatible hprofile)
  have hmem := oneHighGraphSourcePairing_mem_compatible G hfree hv p
    (p.branchLabel q.u)
  rw [q.reverse_pairing_eq_singleton huEdge, q.s_label] at hmem
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
