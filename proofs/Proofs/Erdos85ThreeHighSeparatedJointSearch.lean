import Proofs.Erdos85ThreeHighClosedCoverGate
import Proofs.Erdos85ThreeHighSeparatedGate

namespace Erdos85

/-- Compute closure once, then check all residual coverage before any cover recursion. -/
def threeHighSeparatedJointSearch (B : Fin 24 → Fin 24 → Bool) : Bool :=
  let D := threeHighTripleSupportClosure B
    (fun k => (threeHighCanonicalTripleShapes k).filter (threeHighTripleNoCommonNeighbor B))
  threeHighListedCoverGate D threeHighCanonicalResidual &&
    ((List.finRange 3).all (fun k => threeHighSeparatedGate (D k) (threeHighCanonicalResidual k))) &&
    threeHighListedJointSearch B D threeHighCanonicalResidual

theorem threeHighSeparatedJointSearch_sound : ThreeHighTerminalSound threeHighSeparatedJointSearch := by
  intro B h
  obtain ⟨F,hF,hblocks,hcompat,hcap⟩ := h
  have hD : ∀ k S, S ∈ F k → S ∈ threeHighTripleSupportClosure B
      (fun k => (threeHighCanonicalTripleShapes k).filter (threeHighTripleNoCommonNeighbor B)) k := by
    apply threeHighTripleSupportClosure_preserves B _ F _ (fun i j _ => hcompat i j)
    intro k S hS
    rw [threeHighCanonicalTripleShapes_filter]
    apply List.mem_filter.mpr
    refine ⟨?_, hblocks k S hS⟩
    rw [threeHighDirectTripleList_eq]
    exact (mem_threeHighEligibleTripleList B _ S).mpr
      (((mem_threeHighResolutionDomain B _ (F k)).mp (hF k)).1 hS)
  unfold threeHighSeparatedJointSearch
  simp only [Bool.and_eq_true]
  refine ⟨⟨threeHighListedCoverGate_of_families _ _ F hD ?_, ?_⟩, ?_⟩
  · intro k
    exact ((mem_threeHighResolutionDomain B _ (F k)).mp (hF k)).2.2.2
  · apply List.all_eq_true.mpr
    intro k _
    exact threeHighSeparatedGate_of_resolution B _ _ (F k) (hF k) (hD k)
  · exact threeHighListedJointSearch_of_families B _ _ F hF hD
      (fun i j _ => hcompat i j) hcap

end Erdos85
#print axioms Erdos85.threeHighSeparatedJointSearch_sound
