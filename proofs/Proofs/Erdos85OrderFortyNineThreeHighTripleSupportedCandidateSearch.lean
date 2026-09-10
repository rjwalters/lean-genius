import Proofs.Erdos85ThreeHighListedJointSearch
import Proofs.Erdos85OrderFortyNineThreeHighTripleCompactCandidateSearch
import Proofs.Erdos85OrderFortyNineThreeHighTripleTerminalCertificate

namespace Erdos85

def threeHighFullSupportedCandidateSearch (n : Nat) (p : ThreeBlockFirstRowParameters)
    (q : ThreeHighSecondaryTuple) : Bool :=
  threeHighCrossPrunedDFS (threeHighFullUnionAdj (threeBlockFirstRowEmbed p))
    (threeHighSecondaryTupleAdj q) fun cross =>
      threeHighSupportedJointSearch
        (threeHighEmptyAdj (threeHighFullUnionAdj (threeBlockFirstRowEmbed p))
          (threeHighSecondaryTupleAdj q) cross) n

def threeHighDeficientSupportedCandidateSearch (n : Nat) (p : ThreeBlockDeficientFirstRowParameters)
    (q : ThreeHighSecondaryTuple) : Bool :=
  threeHighCrossPrunedDFS (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p))
    (threeHighSecondaryTupleAdj q) fun cross =>
      threeHighSupportedJointSearch
        (threeHighEmptyAdj (threeHighDeficientUnionAdj (threeBlockDeficientFirstRowEmbed p))
          (threeHighSecondaryTupleAdj q) cross) n

/-- Zero support passes recover exactly the reviewed compact search. -/
theorem threeHighSupportedJointSearch_zero (B : Fin 24 → Fin 24 → Bool) :
    threeHighSupportedJointSearch B 0 =
      threeHighPrunedJointResolutionSearch B threeHighCanonicalResidual threeHighCanonicalRow := by
  simp only [threeHighSupportedJointSearch, threeHighTripleSupportRounds,
    threeHighListedJointSearch, threeHighCanonicalTripleShapes_filter,
    threeHighPrunedJointResolutionSearch, threeHighBlockFamilySearch,
    threeHighPrunedBlockFamilySearch]

theorem threeHighFullSupportedCandidateSearch_zero (p : ThreeBlockFirstRowParameters)
    (q : ThreeHighSecondaryTuple) :
    threeHighFullSupportedCandidateSearch 0 p q = threeHighFullCompactCandidateSearch p q := by
  simp only [threeHighFullSupportedCandidateSearch, threeHighFullCompactCandidateSearch,
    threeHighSupportedJointSearch_zero]

theorem threeHighDeficientSupportedCandidateSearch_zero (p : ThreeBlockDeficientFirstRowParameters)
    (q : ThreeHighSecondaryTuple) :
    threeHighDeficientSupportedCandidateSearch 0 p q = threeHighDeficientCompactCandidateSearch p q := by
  simp only [threeHighDeficientSupportedCandidateSearch, threeHighDeficientCompactCandidateSearch,
    threeHighSupportedJointSearch_zero]

theorem threeHighSupportedJointSearch_sound (n : Nat) :
    ThreeHighTerminalSound (fun B => threeHighSupportedJointSearch B n) := by
  intro B h
  obtain ⟨F,hF,hblocks,hcompat,hcap⟩ := h
  exact threeHighSupportedJointSearch_of_families B n F hF hblocks
    (fun i j _ => hcompat i j) hcap

/- Both universal rejection hypotheses remain explicit, unproved obligations. -/
theorem threeHigh_triple_excluded_of_supported_search_certificates (n : Nat)
    (hfull : ∀ p, threeBlockFirstRowEmbed p ∈ threeBlockFullCandidates → ∀ q ∈ threeHighSecondaryDomain,
      threeHighFullSupportedCandidateSearch n p q = false)
    (hdeficient : ∀ p, threeBlockDeficientFirstRowEmbed p ∈ threeBlockDeficientCandidates → ∀ q ∈ threeHighSecondaryDomain,
      threeHighDeficientSupportedCandidateSearch n p q = false)
    (G : SimpleGraph (Fin 49)) [DecidableRel G.Adj]
    [DecidableRel (antipodalGraph G).Adj]
    [DecidableRel (triangleFreeEdgeGraph G).Adj]
    (hfree : ¬ containsC4 (Fin 49) G)
    (hmin : ∀ x : Fin 49, 7 ≤ G.degree x)
    (hHigh : (orderFortyNineHighVertices G).card = 3)
    (hone : orderFortyNineHighIncidenceCount G 3 = 1)
    (z : Fin 49) (hz : (orderFortyNineHighSupport G z).card = 3) : False := by
  apply threeHigh_triple_excluded_of_terminal_certificates
    (fun B => threeHighSupportedJointSearch B n) (threeHighSupportedJointSearch_sound n)
    ?_ ?_ G hfree hmin hHigh hone z hz
  · simpa only [threeHighFullTerminalCandidateSearch, threeHighFullSupportedCandidateSearch] using hfull
  · simpa only [threeHighDeficientTerminalCandidateSearch, threeHighDeficientSupportedCandidateSearch] using hdeficient

end Erdos85
#print axioms Erdos85.threeHighSupportedJointSearch_zero
#print axioms Erdos85.threeHighFullSupportedCandidateSearch_zero
#print axioms Erdos85.threeHighDeficientSupportedCandidateSearch_zero

#print axioms Erdos85.threeHighSupportedJointSearch_sound
#print axioms Erdos85.threeHigh_triple_excluded_of_supported_search_certificates
