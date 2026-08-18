import Proofs.Erdos85OneHighGraphKnownSector
import Proofs.Erdos85OneHighGraphPairingMultiplicity
import Proofs.Erdos85OneHighPairingSectorTransport

/-! # Known parity sectors for global graph multiplicities -/

namespace Erdos85

noncomputable section

private theorem fst_le_snd_of_mem_oneHighCanonicalLabelPairs
    {pair : OneHighLabelPair} (hpair : pair ∈ oneHighCanonicalLabelPairs) :
    pair.1 ≤ pair.2 := by
  rw [oneHighCanonicalLabelPairs, List.mem_flatMap] at hpair
  obtain ⟨i, hi, hpair⟩ := hpair
  rw [List.mem_filterMap] at hpair
  obtain ⟨j, hj, hpair⟩ := hpair
  split at hpair
  · next hle =>
      simp only [Option.some.injEq] at hpair
      subst pair
      exact hle
  · simp at hpair

private theorem canonical_pair_ne_of_ne {a b : Fin 8} (h : a ≠ b) :
    (min a b, max a b).1 ≠ (min a b, max a b).2 := by
  intro heq
  apply h
  apply le_antisymm
  · calc
      a ≤ max a b := le_max_left _ _
      _ = min a b := heq.symm
      _ ≤ b := min_le_right _ _
  · calc
      b ≤ max a b := le_max_right _ _
      _ = min a b := heq.symm
      _ ≤ a := min_le_left _ _

/-- The complete sector classification only inspects off-diagonal keys, so
off-diagonal multiplicity agreement suffices for transport. -/
theorem oneHighRefinementKnownParitySectorProp_transport_offDiagonal
    {refinement : List (List OneHighLabelPair)}
    {multiplicity : OneHighLabelPair → Nat}
    (hmultiplicity : ∀ pair ∈ oneHighCanonicalLabelPairs,
      pair.1 ≠ pair.2 →
      oneHighPairingRefinementMultiplicity refinement pair = multiplicity pair)
    (hsector : OneHighRefinementKnownParitySectorProp refinement) :
    OneHighMultiplicityKnownParitySectorProp multiplicity := by
  rcases hsector with heven | hmate | hturn | hcross
  · left
    intro pair hpair hne
    rw [← hmultiplicity pair hpair hne]
    exact heven pair hpair hne
  · right; left
    obtain ⟨i, hi⟩ := hmate
    simp only [oneHighCanonicalLabelPair] at hi
    refine ⟨i, ?_⟩
    simp only [oneHighCanonicalLabelPair]
    rw [← hmultiplicity _ (oneHigh_minMax_mem_canonicalLabelPairs _ _) ?_]
    · exact hi
    · fin_cases i <;> decide
  · right; right; left
    obtain ⟨a, b, c, hab, hbc, hac, habOdd, hbcOdd⟩ := hturn
    simp only [oneHighCanonicalLabelPair] at habOdd hbcOdd
    refine ⟨a, b, c, hab, hbc, hac, ?_, ?_⟩
    · simp only [oneHighCanonicalLabelPair]
      rw [← hmultiplicity _ (oneHigh_minMax_mem_canonicalLabelPairs _ _) ?_]
      · exact habOdd
      · apply canonical_pair_ne_of_ne
        intro heq
        exact hab (congrArg oneHighLabelPairColor heq)
    · simp only [oneHighCanonicalLabelPair]
      rw [← hmultiplicity _ (oneHigh_minMax_mem_canonicalLabelPairs _ _) ?_]
      · exact hbcOdd
      · apply canonical_pair_ne_of_ne
        intro heq
        exact hbc (congrArg oneHighLabelPairColor heq)
  · right; right; right
    obtain ⟨i, j, hij, hll, hlh, hhl, hhh⟩ := hcross
    simp only [oneHighCanonicalLabelPair] at hll hlh hhl hhh
    refine ⟨i, j, hij, ?_, ?_, ?_, ?_⟩
    · simp only [oneHighCanonicalLabelPair]
      rw [← hmultiplicity _ (oneHigh_minMax_mem_canonicalLabelPairs _ _) ?_]
      · exact hll
      · apply canonical_pair_ne_of_ne
        intro heq
        have := congrArg Fin.val heq
        simp [oneHighStandardPairLow] at this
        omega
    · simp only [oneHighCanonicalLabelPair]
      rw [← hmultiplicity _ (oneHigh_minMax_mem_canonicalLabelPairs _ _) ?_]
      · exact hlh
      · apply canonical_pair_ne_of_ne
        intro heq
        have := congrArg Fin.val heq
        simp [oneHighStandardPairLow, oneHighStandardPairHigh] at this
        omega
    · simp only [oneHighCanonicalLabelPair]
      rw [← hmultiplicity _ (oneHigh_minMax_mem_canonicalLabelPairs _ _) ?_]
      · exact hhl
      · apply canonical_pair_ne_of_ne
        intro heq
        have := congrArg Fin.val heq
        simp [oneHighStandardPairLow, oneHighStandardPairHigh] at this
        omega
    · simp only [oneHighCanonicalLabelPair]
      rw [← hmultiplicity _ (oneHigh_minMax_mem_canonicalLabelPairs _ _) ?_]
      · exact hhh
      · apply canonical_pair_ne_of_ne
        intro heq
        have := congrArg Fin.val heq
        simp [oneHighStandardPairHigh] at this
        omega

/-- Universal known-sector coverage of the relevant miss table forces the
same complete sector split on the graph's global exchanged-miss
multiplicity. -/
theorem oneHighGraphExchangedMultiplicity_hasKnownParitySector
    {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hfree : ¬ containsC4 V G) {v : V} (hv : G.degree v = 8)
    (p : OneHighRawV2Presentation G hfree v)
    (hcovered :
      oneHighTableKnownParitySectorsCoveredByParity p.profile
        (oneHighGraphRelevantMissTable
          (oneHighRelabeledLeafGraph G v
            (oneHighLeafFinFortyEquiv G hfree v p.branchLabel p.leafLabel))
          p.profile) = true) :
    OneHighMultiplicityKnownParitySectorProp
      (exchangedMissPairMultiplicity
        (oneHighGlobalInternalMate G hfree v)
        (fun x => p.branchLabel
          (oneHighGlobalMissLabel G hfree hv p.external_empty p.outer_degree
            p.mate p.mate_adj x))) := by
  apply oneHighRefinementKnownParitySectorProp_transport_offDiagonal
    (refinement := oneHighGraphPairingRefinement G hfree hv p)
  · intro pair hpair hne
    apply oneHighGraphPairingRefinementMultiplicity_eq_global
    have hle := fst_le_snd_of_mem_oneHighCanonicalLabelPairs hpair
    exact lt_of_le_of_ne hle hne
  · apply (oneHighRefinementHasKnownParitySector_eq_true_iff_prop _).mp
    exact oneHighGraphPairingRefinement_hasKnownParitySector
      G hfree hv p hcovered

end

end Erdos85
