import Proofs.Erdos85OneHighPairingRefinement

/-! # Membership constructors for local pairing shapes -/

namespace Erdos85

/-- Canonicalizing any two labels gives one of the 36 enumerated unordered
label pairs, including diagonal pairs. -/
theorem oneHigh_minMax_mem_canonicalLabelPairs (a b : Fin 8) :
    (min a b, max a b) ∈ oneHighCanonicalLabelPairs := by
  rw [oneHighCanonicalLabelPairs, List.mem_flatMap]
  refine ⟨min a b, ?_, ?_⟩
  · rw [List.mem_ofFn]
    exact ⟨min a b, rfl⟩
  · rw [List.mem_filterMap]
    refine ⟨max a b, ?_, ?_⟩
    · rw [List.mem_ofFn]
      exact ⟨max a b, rfl⟩
    · simp

/-- Every enumerated label pair is admitted as the unique edge of a
one-edge source branch. -/
theorem oneHigh_singleton_mem_sourcePairingShapes
    {profile : Nat} {source : Fin 8} {pair : OneHighLabelPair}
    (hedges : oneHighFamilyInternalEdges profile source = 1)
    (hpair : pair ∈ oneHighCanonicalLabelPairs) :
    [pair] ∈ oneHighSourcePairingShapes profile source := by
  simp [oneHighSourcePairingShapes, hedges, hpair]

/-- Two enumerated pairs, sorted by their numeric codes, are admitted as the
two edges of a two-edge source branch. -/
theorem oneHigh_pair_mem_sourcePairingShapes
    {profile : Nat} {source : Fin 8} {first second : OneHighLabelPair}
    (hedges : oneHighFamilyInternalEdges profile source ≠ 1)
    (hfirst : first ∈ oneHighCanonicalLabelPairs)
    (hsecond : second ∈ oneHighCanonicalLabelPairs)
    (hcode : oneHighLabelPairCode first ≤ oneHighLabelPairCode second) :
    [first, second] ∈ oneHighSourcePairingShapes profile source := by
  simp [oneHighSourcePairingShapes, hedges, hfirst, hsecond, hcode]

/-- Local compatibility membership separates cleanly into the shape and the
endpoint-count equation checks. -/
theorem oneHigh_mem_compatibleSourcePairings_iff
    (profile : Nat) (table : OneHighMissTable) (source : Fin 8)
    (pairs : List OneHighLabelPair) :
    pairs ∈ oneHighCompatibleSourcePairings profile table source ↔
      pairs ∈ oneHighSourcePairingShapes profile source ∧
        oneHighSourcePairingCompatible table source pairs = true := by
  simp [oneHighCompatibleSourcePairings]

end Erdos85
