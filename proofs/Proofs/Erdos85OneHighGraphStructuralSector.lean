import Proofs.Erdos85PairingIncidenceParity
import Proofs.Erdos85MatchingPairingMultiplicity
import Proofs.Erdos85OneHighMissLabelFiber
import Proofs.Erdos85OneHighMultiplicitySectorSupport
import Proofs.Erdos85OneHighPairingSectorInventory
import Proofs.Erdos85OneHighRootPairDecoder

/-! # Structural parity sectors for one-high graph matchings -/

namespace Erdos85

noncomputable section

open scoped BigOperators

private theorem decode_distinct_oneHighRootPair_fiber
    {a c : Fin 8} (hne : a ≠ c)
    (hpair : oneHighRootPair a = oneHighRootPair c) :
    ∃ i : Fin 4,
      (a = oneHighStandardPairLow i ∧ c = oneHighStandardPairHigh i) ∨
      (a = oneHighStandardPairHigh i ∧ c = oneHighStandardPairLow i) := by
  fin_cases a <;> fin_cases c <;>
    simp_all [oneHighRootPair, oneHighStandardPairLow,
      oneHighStandardPairHigh] <;> decide

private theorem fst_le_snd_of_mem_canonicalLabelPairs_structural
    {pair : OneHighLabelPair} (hpair : pair ∈ oneHighCanonicalLabelPairs) :
    pair.1 ≤ pair.2 := by
  rw [oneHighCanonicalLabelPairs, List.mem_flatMap] at hpair
  obtain ⟨i, _, hpair⟩ := hpair
  rw [List.mem_filterMap] at hpair
  obtain ⟨j, _, hpair⟩ := hpair
  split at hpair
  · next hij =>
      simp only [Option.some.injEq] at hpair
      subst pair
      exact hij
  · simp at hpair

@[simp] private theorem oneHighRootPair_standardPairLow (i : Fin 4) :
    oneHighRootPair (oneHighStandardPairLow i) = i := by
  fin_cases i <;> rfl

@[simp] private theorem oneHighRootPair_standardPairHigh (i : Fin 4) :
    oneHighRootPair (oneHighStandardPairHigh i) = i := by
  fin_cases i <;> rfl

private theorem oneHighMultiplicityOddCrossBlockProp_of_four
    {m : OneHighLabelPair → Nat} {i j : Fin 4} (hij : i ≠ j)
    (hll : Odd (m (oneHighCanonicalLabelPair
      (oneHighStandardPairLow i) (oneHighStandardPairLow j))))
    (hlh : Odd (m (oneHighCanonicalLabelPair
      (oneHighStandardPairLow i) (oneHighStandardPairHigh j))))
    (hhl : Odd (m (oneHighCanonicalLabelPair
      (oneHighStandardPairHigh i) (oneHighStandardPairLow j))))
    (hhh : Odd (m (oneHighCanonicalLabelPair
      (oneHighStandardPairHigh i) (oneHighStandardPairHigh j)))) :
    OneHighMultiplicityOddCrossBlockProp m := by
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact ⟨i, j, hij, hll, hlh, hhl, hhh⟩
  · refine ⟨j, i, hji, ?_, ?_, ?_, ?_⟩
    · simpa [oneHighCanonicalLabelPair, min_comm, max_comm] using hll
    · simpa [oneHighCanonicalLabelPair, min_comm, max_comm] using hhl
    · simpa [oneHighCanonicalLabelPair, min_comm, max_comm] using hlh
    · simpa [oneHighCanonicalLabelPair, min_comm, max_comm] using hhh

private theorem normalize_oneHighRootPair_cross
    {m : OneHighLabelPair → Nat} {a b c d : Fin 8}
    (hac : a ≠ c) (hbd : b ≠ d)
    (hpairAC : oneHighRootPair a = oneHighRootPair c)
    (hpairBD : oneHighRootPair b = oneHighRootPair d)
    (hpairAB : oneHighRootPair a ≠ oneHighRootPair b)
    (hab : Odd (m (min a b, max a b)))
    (had : Odd (m (min a d, max a d)))
    (hcb : Odd (m (min c b, max c b)))
    (hcd : Odd (m (min c d, max c d))) :
    OneHighMultiplicityOddCrossBlockProp m := by
  obtain ⟨i, hi | hi⟩ :=
    decode_distinct_oneHighRootPair_fiber hac hpairAC
  · obtain ⟨j, hj | hj⟩ :=
      decode_distinct_oneHighRootPair_fiber hbd hpairBD
    · rcases hi with ⟨rfl, rfl⟩
      rcases hj with ⟨rfl, rfl⟩
      apply oneHighMultiplicityOddCrossBlockProp_of_four
        (by simpa using hpairAB)
      · simpa [oneHighCanonicalLabelPair] using hab
      · simpa [oneHighCanonicalLabelPair] using had
      · simpa [oneHighCanonicalLabelPair] using hcb
      · simpa [oneHighCanonicalLabelPair] using hcd
    · rcases hi with ⟨rfl, rfl⟩
      rcases hj with ⟨rfl, rfl⟩
      apply oneHighMultiplicityOddCrossBlockProp_of_four
        (by simpa using hpairAB)
      · simpa [oneHighCanonicalLabelPair] using had
      · simpa [oneHighCanonicalLabelPair] using hab
      · simpa [oneHighCanonicalLabelPair] using hcd
      · simpa [oneHighCanonicalLabelPair] using hcb
  · obtain ⟨j, hj | hj⟩ :=
      decode_distinct_oneHighRootPair_fiber hbd hpairBD
    · rcases hi with ⟨rfl, rfl⟩
      rcases hj with ⟨rfl, rfl⟩
      apply oneHighMultiplicityOddCrossBlockProp_of_four
        (by simpa using hpairAB)
      · simpa [oneHighCanonicalLabelPair] using hcb
      · simpa [oneHighCanonicalLabelPair] using hcd
      · simpa [oneHighCanonicalLabelPair] using hab
      · simpa [oneHighCanonicalLabelPair] using had
    · rcases hi with ⟨rfl, rfl⟩
      rcases hj with ⟨rfl, rfl⟩
      apply oneHighMultiplicityOddCrossBlockProp_of_four
        (by simpa using hpairAB)
      · simpa [oneHighCanonicalLabelPair] using hcd
      · simpa [oneHighCanonicalLabelPair] using hcb
      · simpa [oneHighCanonicalLabelPair] using had
      · simpa [oneHighCanonicalLabelPair] using hab

theorem exchangedMissPairMultiplicity_diagonal_eq_zero
    {X L : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    [Fintype L] [DecidableEq L] [LinearOrder L]
    (mate : X → X) (label : X → L) (i : L) :
    exchangedMissPairMultiplicity mate label (i, i) = 0 := by
  unfold exchangedMissPairMultiplicity nonconstantMatchingEdgeSources
  apply Finset.card_eq_zero.mpr
  simp only [Finset.filter_eq_empty_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]
  intro x hx
  simp only [exchangedMissPairKey, Prod.mk.injEq]
  intro hkey
  apply hx.2
  apply le_antisymm
  · calc
      label x ≤ max (label x) (label (mate x)) := le_max_left _ _
      _ = i := hkey.2
      _ = min (label x) (label (mate x)) := hkey.1.symm
      _ ≤ label (mate x) := min_le_right _ _
  · calc
      label (mate x) ≤ max (label x) (label (mate x)) := le_max_right _ _
      _ = i := hkey.2
      _ = min (label x) (label (mate x)) := hkey.1.symm
      _ ≤ label x := min_le_left _ _

/-- Even label fibers in a fixed-point-free matching make the off-diagonal
exchanged-key support Eulerian. -/
theorem even_exchangedMultiplicity_incidence_of_even_label_fibers
    {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    (mate : X → X) (label : X → Fin 8)
    (hinv : Function.Involutive mate) (hfree : ∀ x, mate x ≠ x)
    (hfiberEven : ∀ i, Even (matchingLabelFiber label i).card) :
    ∀ i, Even (∑ j,
      exchangedMissPairMultiplicity mate label (min i j, max i j)) := by
  intro i
  let pairs := matchingPairingListSorted mate label
  have hcanonical : ∀ pair ∈ pairs, pair.1 ≤ pair.2 := by
    intro pair hpair
    have hmem := mem_matchingPairingListSorted_canonical mate label hpair
    rw [oneHighCanonicalLabelPairs, List.mem_flatMap] at hmem
    obtain ⟨a, _, hmem⟩ := hmem
    rw [List.mem_filterMap] at hmem
    obtain ⟨b, _, hmem⟩ := hmem
    split at hmem
    · next hab =>
        simp only [Option.some.injEq] at hmem
        subst pair
        exact hab
    · simp at hmem
  have hendpoint : Even (oneHighPairingEndpointCount pairs i) := by
    rw [matchingPairingListSorted_endpointCount mate label i hinv hfree]
    exact hfiberEven i
  have hoff : Even (∑ j ∈ (Finset.univ.erase i),
      exchangedMissPairMultiplicity mate label (min i j, max i j)) := by
    have hpairsEven :=
      (even_incident_pairingMultiplicity_iff_even_endpointCount
        pairs hcanonical i).2 hendpoint
    rw [show (∑ j ∈ (Finset.univ.erase i),
        exchangedMissPairMultiplicity mate label (min i j, max i j)) =
        ∑ j ∈ (Finset.univ.erase i),
          pairs.count (min i j, max i j) by
      apply Finset.sum_congr rfl
      intro j hj
      symm
      apply matchingPairingListSorted_count_eq_exchangedMissPairMultiplicity_of_lt
      exact min_lt_max.mpr (Ne.symm (Finset.mem_erase.mp hj).1)]
    exact hpairsEven
  have hdiag : exchangedMissPairMultiplicity mate label (i, i) = 0 := by
    exact exchangedMissPairMultiplicity_diagonal_eq_zero mate label i
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin 8))
    (fun j => exchangedMissPairMultiplicity mate label (min i j, max i j))
    (Finset.mem_univ i)]
  simp only [min_self, max_self, hdiag, add_zero]
  exact hoff

private theorem card_matchingLabelFiber_equiv_comp_structural
    {X L K : Type*} [Fintype X] [DecidableEq X]
    [DecidableEq L] [DecidableEq K]
    (e : L ≃ K) (label : X → L) (k : K) :
    (matchingLabelFiber (fun x => e (label x)) k).card =
      (matchingLabelFiber label (e.symm k)).card := by
  congr 1
  ext x
  simp only [matchingLabelFiber, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    apply e.injective
    simpa using h
  · intro h
    simpa [h]

/-- The relabeled global exchanged-miss multiplicity of a raw one-high graph
has even incidence at every one of its eight labels. -/
theorem even_oneHighGraphExchangedMultiplicity_incidence
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (hneigh : ∀ y, G.Adj v y → G.degree y = 7)
    (hlocal : ∀ u : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree u = 1)
    (p : OneHighRawV2Presentation G hfree v) :
    ∀ i : Fin 8, Even (∑ j,
      exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x))
        (min i j, max i j)) := by
  apply even_exchangedMultiplicity_incidence_of_even_label_fibers
    (oneHighGlobalInternalMate G hfree v)
    (fun x => p.branchLabel
      (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
        p.mate p.mate_adj x))
    (oneHighGlobalInternalMate_involutive G hfree v)
    (oneHighGlobalInternalMate_ne G hfree v)
  intro i
  rw [card_matchingLabelFiber_equiv_comp_structural]
  exact even_card_oneHighGlobalMissLabelFiber
    G hfree hv hneigh hlocal p.external_empty p.mate p.mate_adj
      p.mate_involutive p.outer_degree (p.branchLabel.symm i)

/-- If the two labels in each canonical root mate-pair have even exchanged
multiplicity, Eulerian incidence leaves only the all-even, three-pair-turn,
and complete two-pair cross patterns. -/
theorem oneHighGraphExchangedMultiplicity_allEven_or_turn_or_cross
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (hneigh : ∀ y, G.Adj v y → G.degree y = 7)
    (hlocal : ∀ u : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree u = 1)
    (p : OneHighRawV2Presentation G hfree v)
    (hsame : ∀ a b : Fin 8, oneHighRootPair a = oneHighRootPair b →
      Even (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x))
        (min a b, max a b))) :
    let m := exchangedMissPairMultiplicity
      (oneHighGlobalInternalMate G hfree v)
      (fun x => p.branchLabel
        (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
          p.mate p.mate_adj x))
    (∀ a b, a ≠ b → Even (m (min a b, max a b))) ∨
      (∃ a b c,
        oneHighRootPair a ≠ oneHighRootPair b ∧
        oneHighRootPair b ≠ oneHighRootPair c ∧
        oneHighRootPair a ≠ oneHighRootPair c ∧
        Odd (m (min a b, max a b)) ∧
        Odd (m (min b c, max b c))) ∨
      (∃ a b c d,
        a ≠ c ∧ b ≠ d ∧
        oneHighRootPair a = oneHighRootPair c ∧
        oneHighRootPair b = oneHighRootPair d ∧
        oneHighRootPair a ≠ oneHighRootPair b ∧
        Odd (m (min a b, max a b)) ∧
        Odd (m (min a d, max a d)) ∧
        Odd (m (min c b, max c b)) ∧
        Odd (m (min c d, max c d))) := by
  dsimp only
  apply odd_support_three_color_turn_or_cross oneHighRootPair
  · exact three_same_oneHighRootPair_not_pairwise_distinct
  · exact even_oneHighGraphExchangedMultiplicity_incidence
      G hfree hv hneigh hlocal p
  · intro i
    rw [exchangedMissPairMultiplicity_diagonal_eq_zero]
    exact Even.zero
  · exact hsame

/-- Unconditional structural split, before normalizing the arbitrary
two-point color fibers in the cross case to their standard low/high names. -/
theorem oneHighGraphExchangedMultiplicity_structural_split
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (hneigh : ∀ y, G.Adj v y → G.degree y = 7)
    (hlocal : ∀ u : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree u = 1)
    (p : OneHighRawV2Presentation G hfree v) :
    let m := exchangedMissPairMultiplicity
      (oneHighGlobalInternalMate G hfree v)
      (fun x => p.branchLabel
        (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
          p.mate p.mate_adj x))
    (∀ a b, a ≠ b → Even (m (min a b, max a b))) ∨
      (∃ i : Fin 4, Odd (m (oneHighCanonicalLabelPair
        (oneHighStandardPairLow i) (oneHighStandardPairHigh i)))) ∨
      (∃ a b c,
        oneHighRootPair a ≠ oneHighRootPair b ∧
        oneHighRootPair b ≠ oneHighRootPair c ∧
        oneHighRootPair a ≠ oneHighRootPair c ∧
        Odd (m (min a b, max a b)) ∧
        Odd (m (min b c, max b c))) ∨
      (∃ a b c d,
        a ≠ c ∧ b ≠ d ∧
        oneHighRootPair a = oneHighRootPair c ∧
        oneHighRootPair b = oneHighRootPair d ∧
        oneHighRootPair a ≠ oneHighRootPair b ∧
        Odd (m (min a b, max a b)) ∧
        Odd (m (min a d, max a d)) ∧
        Odd (m (min c b, max c b)) ∧
        Odd (m (min c d, max c d))) := by
  dsimp only
  let mate := oneHighGlobalInternalMate G hfree v
  let label := fun x => p.branchLabel
    (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
      p.mate p.mate_adj x)
  let m := exchangedMissPairMultiplicity mate label
  by_cases hmate : ∃ i : Fin 4, Odd (m (oneHighCanonicalLabelPair
      (oneHighStandardPairLow i) (oneHighStandardPairHigh i)))
  · exact Or.inr (Or.inl hmate)
  have hsame : ∀ a b : Fin 8, oneHighRootPair a = oneHighRootPair b →
      Even (m (min a b, max a b)) := by
    intro a b hab
    by_cases heq : a = b
    · subst b
      simp only [min_self, max_self]
      dsimp only [m]
      rw [exchangedMissPairMultiplicity_diagonal_eq_zero]
      exact Even.zero
    · have hnotOdd : ¬ Odd (m (min a b, max a b)) := by
        intro hodd
        apply hmate
        have habCases :=
          (oneHighRootPair_eq_iff_eq_or_standardMate a b).mp hab
        rcases habCases with habEq | habMate
        · exact (heq habEq).elim
        · refine ⟨oneHighRootPair b, ?_⟩
          rw [habMate] at hodd
          fin_cases b <;> exact hodd
      exact Nat.not_odd_iff_even.mp hnotOdd
  obtain hall | hturn | hcross :=
    oneHighGraphExchangedMultiplicity_allEven_or_turn_or_cross
      G hfree hv hneigh hlocal p hsame
  · exact Or.inl hall
  · exact Or.inr (Or.inr (Or.inl hturn))
  · exact Or.inr (Or.inr (Or.inr hcross))

/-- The complete four-way known-sector theorem for the actual global
exchanged-miss multiplicity.  Unlike the finite-table consumer, this result
has no inventory-coverage hypothesis. -/
theorem oneHighGraphExchangedMultiplicity_hasKnownParitySector_structural
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (hneigh : ∀ y, G.Adj v y → G.degree y = 7)
    (hlocal : ∀ u : {z : V // z ∈ G.neighborSet v},
      (G.induce (G.neighborSet v)).degree u = 1)
    (p : OneHighRawV2Presentation G hfree v) :
    OneHighMultiplicityKnownParitySectorProp
      (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x))) := by
  let m := exchangedMissPairMultiplicity
    (oneHighGlobalInternalMate G hfree v)
    (fun x => p.branchLabel
      (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
        p.mate p.mate_adj x))
  obtain hall | hmate | hturn | hcross :=
    oneHighGraphExchangedMultiplicity_structural_split
      G hfree hv hneigh hlocal p
  · left
    intro pair hpair hne
    have hle := fst_le_snd_of_mem_canonicalLabelPairs_structural hpair
    simpa [min_eq_left hle, max_eq_right hle] using
      hall pair.1 pair.2 hne
  · exact Or.inr (Or.inl hmate)
  · right; right; left
    obtain ⟨a, b, c, hab, hbc, hac, habOdd, hbcOdd⟩ := hturn
    refine ⟨a, b, c, ?_, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hab ((oneHighLabelPairColor_eq_iff_rootPair_eq a b).1 h)
    · intro h
      exact hbc ((oneHighLabelPairColor_eq_iff_rootPair_eq b c).1 h)
    · intro h
      exact hac ((oneHighLabelPairColor_eq_iff_rootPair_eq a c).1 h)
    · simpa [oneHighCanonicalLabelPair] using habOdd
    · simpa [oneHighCanonicalLabelPair] using hbcOdd
  · right; right; right
    obtain ⟨a, b, c, d, hac, hbd, hpairAC, hpairBD, hpairAB,
      hab, had, hcb, hcd⟩ := hcross
    exact normalize_oneHighRootPair_cross hac hbd hpairAC hpairBD hpairAB
      hab had hcb hcd

end

end Erdos85
