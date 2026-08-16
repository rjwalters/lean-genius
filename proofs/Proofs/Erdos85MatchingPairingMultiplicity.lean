import Proofs.Erdos85MatchingPairingRefinement

/-! # Multiplicity transport for matching-induced pairing lists -/

namespace Erdos85

noncomputable section

/-- On a genuine off-diagonal key, counting the key in the canonical list of
matching edges is exactly the exchanged-key multiplicity used by the graph
parity argument. -/
theorem matchingPairingListSorted_count_eq_exchangedMissPairMultiplicity
    {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    (mate : X → X) (label : X → Fin 8) (key : OneHighLabelPair)
    (hkey : key.1 < key.2) :
    (matchingPairingListSorted mate label).count key =
      exchangedMissPairMultiplicity mate label key := by
  classical
  rw [show (matchingPairingListSorted mate label).count key =
      (matchingPairingList mate label).count key from
    (List.mergeSort_perm (matchingPairingList mate label)
      (fun a b => decide (a ≤ b))).count_eq key]
  rw [List.count_eq_length_filter]
  unfold matchingPairingList
  rw [List.filter_map]
  simp only [List.length_map,
    exchangedMissPairMultiplicity, nonconstantMatchingEdgeSources,
    matchingEdgeSources, exchangedMissPairKey]
  have hn : (List.filter
      ((fun pair : OneHighLabelPair => pair == key) ∘ fun x =>
        (min (label x) (label (mate x)), max (label x) (label (mate x))))
      ((Finset.univ.filter fun x => x < mate x) : Finset X).toList).Nodup :=
    (Finset.nodup_toList
      ((Finset.univ.filter fun x => x < mate x) : Finset X)).filter _
  rw [← List.toFinset_card_of_nodup hn, List.toFinset_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    List.mem_toFinset, Finset.mem_toList, Function.comp_apply, beq_iff_eq]
  change (x < mate x ∧
      (min (label x) (label (mate x)), max (label x) (label (mate x))) = key) ↔
    ((x < mate x ∧ label x ≠ label (mate x)) ∧
      (min (label x) (label (mate x)), max (label x) (label (mate x))) = key)
  constructor
  · intro ⟨hxlt, heq⟩
    refine ⟨⟨hxlt, ?_⟩, heq⟩
    intro hsame
    have hdiag : key.1 = key.2 := by
      rw [← heq]
      simp [hsame]
    exact (ne_of_lt hkey) hdiag
  · rintro ⟨⟨hxlt, _hne⟩, heq⟩
    exact ⟨hxlt, heq⟩

/-- Singleton-refinement form consumed directly by the pairing-sector API. -/
theorem matchingPairingRefinementMultiplicity_eq_exchangedMissPairMultiplicity
    {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    (mate : X → X) (label : X → Fin 8) (key : OneHighLabelPair)
    (hkey : key.1 < key.2) :
    oneHighPairingRefinementMultiplicity
        [matchingPairingListSorted mate label] key =
      exchangedMissPairMultiplicity mate label key := by
  simpa [oneHighPairingRefinementMultiplicity] using
    matchingPairingListSorted_count_eq_exchangedMissPairMultiplicity
      mate label key hkey

end

end Erdos85
