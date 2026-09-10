import Proofs.Erdos85ThreeHighClosedJointSearch

namespace Erdos85

/-- Reject a list collection if a required residual label has no remaining triple. -/
def threeHighListedCoverGate (D : Fin 3 → List (Finset (Fin 24)))
    (R : Fin 3 → Finset (Fin 24)) : Bool :=
  (List.finRange 3).all fun k => (List.finRange 24).all fun x =>
    decide (x ∉ R k) || (D k).any (fun S => decide (x ∈ S))

theorem threeHighListedCoverGate_of_families
    (D : Fin 3 → List (Finset (Fin 24))) (R : Fin 3 → Finset (Fin 24))
    (F : Fin 3 → Finset (Finset (Fin 24)))
    (hmem : ∀ k S, S ∈ F k → S ∈ D k)
    (hcover : ∀ k, (F k).biUnion id = R k) :
    threeHighListedCoverGate D R = true := by
  apply List.all_eq_true.mpr
  intro k _
  apply List.all_eq_true.mpr
  intro x _
  by_cases hx : x ∈ R k
  · have hx' : x ∈ (F k).biUnion id := by rw [hcover]; exact hx
    obtain ⟨S,hS,hxS⟩ := Finset.mem_biUnion.mp hx'
    have ha : (D k).any (fun S => decide (x ∈ S)) = true :=
      List.any_eq_true.mpr ⟨S,hmem k S hS,by simpa using hxS⟩
    simp [ha]
  · simp [hx]

/-- Compute closure once, then check all residual coverage before any cover recursion. -/
def threeHighClosedCoverSearch (B : Fin 24 → Fin 24 → Bool) : Bool :=
  let D := threeHighTripleSupportClosure B
    (fun k => (threeHighCanonicalTripleShapes k).filter (threeHighTripleNoCommonNeighbor B))
  threeHighListedCoverGate D threeHighCanonicalResidual &&
    threeHighListedJointSearch B D threeHighCanonicalResidual

theorem threeHighClosedCoverSearch_sound : ThreeHighTerminalSound threeHighClosedCoverSearch := by
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
  unfold threeHighClosedCoverSearch
  simp only [Bool.and_eq_true]
  refine ⟨threeHighListedCoverGate_of_families _ _ F hD ?_, ?_⟩
  · intro k
    exact ((mem_threeHighResolutionDomain B _ (F k)).mp (hF k)).2.2.2
  · exact threeHighListedJointSearch_of_families B _ _ F hF hD
      (fun i j _ => hcompat i j) hcap

end Erdos85
#print axioms Erdos85.threeHighListedCoverGate_of_families
#print axioms Erdos85.threeHighClosedCoverSearch_sound
