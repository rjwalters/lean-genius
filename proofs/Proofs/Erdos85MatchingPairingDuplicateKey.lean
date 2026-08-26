import Proofs.Erdos85MatchingPairingRefinement

/-! # Duplicate-key matching rows -/

namespace Erdos85

noncomputable section

/-- If the two oriented edges of a matching carry the same canonical key,
then sorting its pairing list leaves exactly two copies of that key. -/
theorem matchingPairingListSorted_eq_duplicate_of_two_sources
    {X : Type*} [Fintype X] [DecidableEq X] [LinearOrder X]
    (mate : X → X) (label : X → Fin 8)
    (key : OneHighLabelPair) (x y : X)
    (hcard : (matchingEdgeSources mate).card = 2)
    (hx : x ∈ matchingEdgeSources mate)
    (hy : y ∈ matchingEdgeSources mate)
    (hxy : x ≠ y)
    (hkeyx : (min (label x) (label (mate x)),
      max (label x) (label (mate x))) = key)
    (hkeyy : (min (label y) (label (mate y)),
      max (label y) (label (mate y))) = key) :
    matchingPairingListSorted mate label = [key, key] := by
  have hsources : matchingEdgeSources mate = {x, y} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · simpa using Finset.insert_subset hx (Finset.singleton_subset_iff.mpr hy)
    · simpa [hxy] using hcard.le
  have hrawLength : (matchingPairingList mate label).length = 2 := by
    simpa using (matchingPairingList_length mate label).trans hcard
  have hall : ∀ pair ∈ matchingPairingList mate label, pair = key := by
    intro pair hpair
    simp only [matchingPairingList, List.mem_map, Finset.mem_toList] at hpair
    rcases hpair with ⟨source, hsource, rfl⟩
    rw [hsources] at hsource
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsource
    rcases hsource with rfl | rfl
    · exact hkeyx
    · exact hkeyy
  obtain ⟨first, second, hraw⟩ := List.length_eq_two.mp hrawLength
  have hfirst : first = key := hall first (by simp [hraw])
  have hsecond : second = key := hall second (by simp [hraw])
  subst first
  subst second
  unfold matchingPairingListSorted
  rw [hraw]
  let rel := fun a b : OneHighLabelPair =>
    decide (oneHighLabelPairCode a ≤ oneHighLabelPairCode b)
  let sorted := [key, key].mergeSort rel
  have hp := List.mergeSort_perm [key, key] rel
  change sorted = [key, key]
  have hsortedLength : sorted.length = 2 := by
    simpa [sorted] using hp.length_eq.symm
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hsortedLength
  have ha : a = key := by
    have hamem : a ∈ sorted := by simp [hab]
    have := hp.mem_iff.mp (by simpa [sorted] using hamem)
    simpa using this
  have hb : b = key := by
    have hbmem : b ∈ sorted := by simp [hab]
    have := hp.mem_iff.mp (by simpa [sorted] using hbmem)
    simpa using this
  simpa [hab, ha, hb]

end

end Erdos85

#print axioms Erdos85.matchingPairingListSorted_eq_duplicate_of_two_sources
